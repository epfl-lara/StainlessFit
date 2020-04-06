package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import extraction._
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, Neq => IRNeq,
  Eq => IREq, Lt => IRLt, Gt => IRGt, Leq => IRLeq, Geq => IRGeq, Nop => IRNop,
  Plus => IRPlus, Minus => IRMinus, Mul => IRMul, Div => IRDiv,
  BooleanLiteral => IRBooleanLiteral, UnitLiteral => IRUnitLiteral,
  NatType => IRNatType, UnitType => IRUnitType, _}

import codegen.llvm._
import codegen.utils.{Identifier => _, _}

class CodeGen(implicit val rc: RunContext) extends Phase[Module] {
  def transform(t: Tree): (Tree, Module) = (t, CodeGen.genLLVM(t, true))
}

object CodeGen {
    def genLLVM(tree: Tree, isMain: Boolean)(implicit rc: RunContext): Module = {

        def cgModule(inputTree: Tree): Module = {
          val lh = new LocalHandler(rc)

          val (defFunctions, body) = extractDefFun(inputTree)

          val functions = defFunctions map cgDefFunction

          val mainReturnType = resultType(body)(lh) match {
            case FunctionReturnType(funName) => functions.filter(_.name == funName).head.returnType
            case otherType => otherType
          }

          val main = cgFunction(mainReturnType, Global("main"), Nil, body)

          Module(
            rc.config.file.getName(),
            main,
            functions)
        }

        def cgDefFunction(defFun: DefFunction): Function = {
          val DefFunction(args, optReturnType, _, bind, _) = defFun

          val params = args.toList.map{
            case TypedArgument(id, tpe) => (id, ParamDef(translateType(tpe), Local(id.name)))
            case arg => rc.reporter.fatalError(s"Unexpected type for arg $arg")
          }

          val (funId, body) = extractBody(bind)

          val returnType = translateType(optReturnType.getOrElse(rc.reporter.fatalError("")))
          cgFunction(returnType, Global(funId.name), params, body)
        }

        def cgFunction(returnType: Type, name: Global, params: List[(Identifier, ParamDef)], body: Tree): Function = {

          val lh = new LocalHandler(rc)
          lh.add(params)

          val function = Function(returnType, name, params.unzip._2)

          val initBlock = lh.newBlock("entry")

          val end = lh.freshLabel("End")
          val result = lh.freshLocal("result")

          val (entryBlock, phi) = codegen(body, initBlock, Some(end), Some(result))(lh, function)
          function.add(entryBlock)

          val endBlock = lh.newBlock(end)
          function.add(endBlock <:> phi <:> Return(Value(result), returnType))
          function
        }

        def extractDefFun(t: Tree): (List[DefFunction], Tree) = t match {
          case defFun @ DefFunction(_, _, _, _, nested) => {
            val (defs, rest) = extractDefFun(nested)
            (defFun +: defs, rest)
          }
          case bind: Bind => extractDefFun(extractBody(bind)._2)

          case rest => (Nil, rest)
        }

        def extractBody(bind: Tree): (Identifier, Tree) = bind match {
          case Bind(id, rec: Bind) => extractBody(rec)
          case Bind(id, body) => (id, body)
          case _ => rc.reporter.fatalError(s"Couldn't find the body in $bind")
        }

        def translateOp(op: Operator): Op = op match {
          case Not => IRNot
          case And => IRAnd
          case Or => IROr
          case Neq => IRNeq
          case Eq => IREq
          case Lt => IRLt
          case Gt => IRGt
          case Leq => IRLeq
          case Geq => IRGeq
          case Nop => IRNop
          case Plus => IRPlus
          case Minus => IRMinus
          case Mul => IRMul
          case Div => IRDiv

          case _ => rc.reporter.fatalError("Not yet implemented")
        }

        def translateType(tpe: Tree): Type = tpe match {
          case BoolType => BooleanType
          case NatType => IRNatType
          case UnitType => IRUnitType
          case Bind(_, rest) => translateType(rest) //TODO Is this necessary
          case _ => rc.reporter.fatalError(s"Unkown type $tpe")
        }

        def translateValue(t: Tree)(implicit lh: LocalHandler): Value = t match {
          case BooleanLiteral(b) => Value(IRBooleanLiteral(b))
          case NatLiteral(n) => Value(Nat(n))
          case UnitLiteral => Value(Nat(0))
          case Var(id) => Value(lh.getLocal(id))
          case _ => rc.reporter.fatalError(s"This tree isn't a value: $t")
        }

        def cgValue(tpe: Type, value: Value, next: Option[Label], toAssign: Option[Local]): List[Instruction] = {
          val assign = toAssign.toList.map(local => Assign(local, tpe, value))
          val jump = next.toList.map(label => Jump(label))

          if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")

          assign ++ jump
        }

        def isValue(t: Tree): Boolean = t match {
          case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral | Var(_) => true
          case _ => false
        }

        def flattenPrimitive(t: Tree): List[Tree] = t match {
          case Primitive(op, args) => args.flatMap{
            case Primitive(op2, args2) if op2 == op => flattenPrimitive(Primitive(op2, args2))
            case other => List(other)
          }

          case _ => rc.reporter.fatalError(s"flattenPrimitive is not defined for $t")
        }

        def flattenParams(t: Tree): List[Tree] = t match {
          //TODO might not be needed at all (flattenApp is what is being used)
          case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral => List(t)
          case Pair(first, second) => first +: flattenParams(second)
          case Primitive(_, _) => List(t)
          case _ => rc.reporter.fatalError(s"flattenParams is not defined fo $t")
        }

        def flattenApp(t: Tree): (Identifier, List[Tree]) = t match {
          case App(Var(id), arg) => (id, List(arg))
          case App(recApp @ App(_, _), arg) => {
            val (id, otherArgs) = flattenApp(recApp)
            (id , otherArgs :+ arg)
          }

          case _ => rc.reporter.fatalError(s"flattenApp is not defined fo $t")
        }

        def resultType(t: Tree)(implicit lh: LocalHandler): Type = t match {
          case BooleanLiteral(_) => BooleanType
          case NatLiteral(_) => IRNatType
          case UnitLiteral => IRUnitType
          case Var(id) => lh.getType(id)

          case Primitive(op, _) => translateOp(op).returnType
          case IfThenElse(_, thenn, _) => resultType(thenn)
          case App(Var(funId), _) => FunctionReturnType(Global(funId.name))
          case app @ App(_, _) => FunctionReturnType(Global(flattenApp(app)._1.name))
          case _ => rc.reporter.fatalError(s"Result type not yet implemented for $t")
        }

        def cgIntermediateBlocks(flatArgs: List[Tree], initialBlock: Block)(implicit lh: LocalHandler, f: Function): (Block, List[Value]) = {

          val argLocals = flatArgs.map{
            case arg if isValue(arg) => Left(translateValue(arg))
            case arg => Right(lh.freshLocal())
          }

          val init: (Block, List[Value]) = (initialBlock, Nil)

          val (cB, valueList: List[Value]) = argLocals.zip(flatArgs).foldLeft(init) {
            case ((currentBlock, values), (Left(value), arg)) => {
              (currentBlock, values :+ value)
            }

            case ((currentBlock, values), (Right(local), arg)) => {
              //TODO check if an intermediate block is necessary (or let it be removed by clang)
              val tempLabel = lh.freshLabel("tempBlock")
              val tempBlock = lh.newBlock(tempLabel)

              val afterLabel = lh.freshLabel("afterBlock")
              val afterBlock = lh.newBlock(afterLabel)

              f.add(currentBlock <:> Jump(tempLabel))

              val (otherBlock, phi) = codegen(arg, tempBlock, Some(afterLabel), Some(local))
              f.add(otherBlock)
              (afterBlock <:> phi, values :+ Value(local))
            }
          }

          (cB, valueList)
        }

        def cgFunctionCall(call: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
          (implicit lh: LocalHandler, f: Function): (Block, List[Instruction]) = {
            val (funId, flatArgs) = flattenApp(call)

            val (cB, valueList) = cgIntermediateBlocks(flatArgs, block)

            val result = toAssign.getOrElse(lh.freshLocal("unused"))

            val jump = next.toList.map(label => Jump(label))
            (cB <:> Call(result, Global(funId.name), valueList) <:> jump, Nil)
          }

        def filterErasable(t: Tree): Tree = t match {
          case LetIn(_, _, _) |
            MacroTypeDecl(_, _) |
            MacroTypeInst(_, _) |
            ErasableApp(_, _) |
            Refl(_, _) |
            Fold(_, _) |
            Unfold(_, _) |
            UnfoldPositive(_, _) |
            DefFunction(_, _, _, _, _) |
            ErasableLambda(_, _) |
            Abs(_) |
            TypeApp(_, _) |
            Because(_, _) => rc.reporter.fatalError(s"This tree should have been erased: $t")

          case _ => t
        }

        def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
          (implicit lh: LocalHandler, f: Function): (Block, List[Instruction]) =

          filterErasable(inputTree) match {

            case value if isValue(value) => (block <:> cgValue(resultType(value), translateValue(value), next, toAssign), Nil)

            case call @ App(_, _) => cgFunctionCall(call, block, next, toAssign)

            case IfThenElse(cond, thenn, elze) => {

              val condLocal = lh.freshLocal()

              val trueLocal = lh.freshLocal()
              val tBlock = lh.newBlock("then")

              val falseLocal = lh.freshLocal()
              val fBlock = lh.newBlock("else")

              val afterLocal = lh.freshLocal()
              val afterBlock = lh.newBlock("after")

              val (condPrep, condPhi) = codegen(cond, block, None, Some(condLocal))

              val (trueBlock, truePhi) = codegen(thenn, tBlock, Some(afterBlock.label), Some(trueLocal))
              f.add(trueBlock)

              val (falseBlock, falsePhi) = codegen(elze, fBlock, Some(afterBlock.label), Some(falseLocal))
              f.add(falseBlock)

              val parentBlock =
                condPrep <:>
                condPhi <:>
                Branch(Value(condLocal), tBlock.label, fBlock.label)

              f.add(parentBlock)

              val nextPhi =
                truePhi ++
                falsePhi ++
                toAssign.toList.map{ //TODO Need a better way to check for the type
                  case local => Phi(local, resultType(thenn), List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label)))
                }

              (afterBlock <:> nextPhi <:> Jump(next.get), Nil)
            }

            case Primitive(op, args) => {

              val flatArgs = flattenPrimitive(inputTree)
              val (cB, valueList) = cgIntermediateBlocks(flatArgs, block)

              val last = valueList.size - 1

              //apply the operation to the arguments two-by-two
              val (resultBlock, result) = valueList.zipWithIndex.tail.foldLeft((cB, valueList.head)){
                case ((cBlock, lhs), (rhs, index)) => {
                  val temp = if(index == last && toAssign.isDefined){
                    toAssign.get
                  } else {
                    lh.freshLocal("temp")
                  }
                  (cBlock <:> BinaryOp(translateOp(op), temp, lhs, rhs), Value(temp))
                }
              }

              val jump = next.toList.map(label => Jump(label))
              (resultBlock <:> jump, Nil)
            }

            case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
          }

        cgModule(tree)
    }
}
