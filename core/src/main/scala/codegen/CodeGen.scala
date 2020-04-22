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
  def transform(t: Tree): (Tree, Module) = (t, CodeGen.genLLVM(t, true, rc.config.file.getName()))
}

object CodeGen {
    def genLLVM(tree: Tree, isMainModule: Boolean, moduleName: String)(implicit rc: RunContext): Module = {

        def cgModule(inputTree: Tree): Module = {
          val lh = new LocalHandler(rc)

          val (defFunctions, body) = extractDefFun(inputTree)

          val functions = defFunctions map cgDefFunction

          val main = cgFunction(IRNatType, Global("main"), Nil, body, true)

          Module(
            moduleName,
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

          val returnType = translateType(optReturnType.getOrElse(rc.reporter.fatalError("No return type found")))

          cgFunction(returnType, Global(funId.name), params, body)
        }

        def cgFunction(returnType: Type, name: Global, params: List[(Identifier, ParamDef)], body: Tree, isMain: Boolean = false): Function = {

          val lh = new LocalHandler(rc)
          lh.add(params)

          val function = Function(returnType, name, params.unzip._2)

          val initBlock = lh.newBlock("entry")

          val end = lh.freshLabel("End")
          val result = lh.freshLocal("result")

          val (entryBlock, phi) = codegen(body, initBlock, Some(end), Some(result))(lh, function)
          function.add(entryBlock)

          val endBlock = lh.newBlock(end)

          val (print, returnValue) = if(isMain){
            val printType = resultType(body)(lh)

            (List(PrintResult(result, printType, lh)), Value(Nat(0)))
          } else {
            (Nil, Value(result))
          }

          function.add(endBlock <:> phi <:> print <:> Return(returnValue, returnType))
          function
        }

        def extractDefFun(t: Tree): (List[DefFunction], Tree) = t match {
          case defFun @ DefFunction(_, _, _, _, nested) => {  //DefFunction(_, _, _, _, Bind(fid, body))
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
        } //Binds(bind: Bind): Option(Seq[Identifier], Tree) unapply est utilisé dans un pattern match

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
          case SigmaType(tpe, bind) => PairType(translateType(tpe), translateType(bind))
          case _ => rc.reporter.fatalError(s"Unable to translate type $tpe")
        }

        def translateValue(t: Tree)(implicit lh: LocalHandler): Value = t match {
          case BooleanLiteral(b) => Value(IRBooleanLiteral(b))
          case NatLiteral(n) => Value(Nat(n))
          case UnitLiteral => Value(Nat(0))
          case Var(id) => Value(lh.getLocal(id))
          case _ => rc.reporter.fatalError(s"This tree isn't a value: $t")
        }

        def cgValue(tpe: Type, value: Value, next: Option[Label], toAssign: Option[Local])
        (implicit lh: LocalHandler): List[Instruction] = {
          val jump = jumpTo(next)
          val assign = List(Assign(assignee(toAssign), tpe, value))
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
          case LetIn(_, _, Bind(_, rest)) => resultType(rest)
          case Primitive(op, _) => translateOp(op).returnType
          case IfThenElse(_, thenn, _) => resultType(thenn)

          case app @ App(_, _) => FunctionReturnType(Global(flattenApp(app)._1.name))

          case Pair(first, second) => PairType(resultType(first), resultType(second))

          case First(pair) => resultType(pair) match {
            case tpe @ FunctionReturnType(_) => FirstType(tpe)
            case PairType(firstType, _) => firstType
            case nested @ FirstType(_) => FirstType(nested)
            case nested @ SecondType(_) => FirstType(nested)
            case other => rc.reporter.fatalError(s"Unexpected operation: calling First on type $other")
          }
          case Second(pair) => resultType(pair) match {
            case tpe @ FunctionReturnType(_) => SecondType(tpe)
            case PairType(_, secondType) => secondType
            case nested @ FirstType(_) => SecondType(nested)
            case nested @ SecondType(_) => SecondType(nested)
            case other => rc.reporter.fatalError(s"Unexpected operation: calling Second on type $other")
          }

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

            val result = assignee(toAssign)

            val jump = jumpTo(next)
            (cB <:> Call(result, Global(funId.name), valueList) <:> jump, Nil)
          }

        def filterErasable(t: Tree): Tree = t match {
          case
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

        def assignee(toAssign: Option[Local])(implicit lh: LocalHandler) = toAssign getOrElse lh.freshLocal
        def jumpTo(next: Option[Label]) = next.toList.map(label => Jump(label))

        def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
          (implicit lh: LocalHandler, f: Function): (Block, List[Instruction]) =

          filterErasable(inputTree) match {

            case value if isValue(value) => (block <:> cgValue(resultType(value), translateValue(value), next, toAssign), Nil)

            case call @ App(_, _) => cgFunctionCall(call, block, next, toAssign)

            case Pair(first, second) => {
              val pair = assignee(toAssign)
              val firstLocal = lh.dot(pair, "first")
              val secondLocal = lh.dot(pair, "second")

              val t1 = lh.dot(pair, "malloc.gep")
              val t2 = lh.dot(pair, "malloc.size")
              val t3 = lh.dot(pair, "malloc")

              val pairType = resultType(inputTree)
              val malloc = Malloc(pair, t1, t2, t3, pairType) //will assigne toAssign

              val (firstBlock, firstPhi) = codegen(first, block <:> malloc, None, Some(firstLocal))
              val (secondBlock, secondPhi) = codegen(second, firstBlock <:> firstPhi, None, Some(secondLocal))

              val (firstPtr, secondPtr) = (lh.dot(pair, "first.gep"), lh.dot(pair, "second.gep"))

              val initialise = List(
                GepToFirst(firstPtr, pairType, pair),
                Store(Value(firstLocal), resultType(first), firstPtr),
                GepToSecond(secondPtr, pairType, pair),
                Store(Value(secondLocal), resultType(second), secondPtr)
              )

              (secondBlock <:> secondPhi <:> initialise <:> jumpTo(next), Nil)
            }

            case First(pair) => { //TODO refactor first and second since they are identical?
              val pairLocal = lh.freshLocal("pair")
              val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal))

              val pairType = resultType(pair)
              val assignLocal = assignee(toAssign)
              val firstPtr = lh.dot(assignLocal, "first.gep")

              val prep = List(
                GepToFirst(firstPtr, pairType, pairLocal),
                Load(assignLocal, resultType(inputTree), firstPtr)
              )

              (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
            }

            case Second(pair) => {

              val pairLocal = lh.freshLocal("pair")
              val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal))

              val assignLocal = assignee(toAssign)

              val pairType = resultType(pair)
              val secondPtr = lh.dot(pairLocal, "second.gep")

              val prep = List(
                GepToSecond(secondPtr, pairType, pairLocal),
                Load(assignLocal, resultType(inputTree), secondPtr)
              )

              (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
            }

            case LetIn(_, valueBody, Bind(newVar, rest)) => {
                val local = lh.freshLocal(newVar)

                val (tempBlock, phi) = codegen(valueBody, block, None, Some(local))
                lh.add(newVar, ParamDef(resultType(valueBody), local))
                codegen(rest, tempBlock <:> phi, next, toAssign)
            }

            case IfThenElse(cond, thenn, elze) => {

              val condLocal = lh.freshLocal("cond")

              val trueLocal = lh.freshLocal("phi")
              val tBlock = lh.newBlock("then")

              val falseLocal = lh.freshLocal("phi")
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
                toAssign.toList.map{
                  case local => Phi(local, resultType(thenn), List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label)))
                }

              val jump = jumpTo(next)
              (afterBlock <:> nextPhi <:> jump, Nil)
            }

            case Primitive(op, args) => {
              val init: (Block, List[Value]) = (block, Nil)
              val (currentBlock, values) = args.map((_, lh.freshLocal("temp"))).foldLeft(init){
                case ((currentBlock, values), (arg, temp)) => {
                  val (nextBlock, phi) = codegen(arg, currentBlock, None, Some(temp))
                  (nextBlock <:> phi, values :+ Value(temp))
                }
              }

              val jump = jumpTo(next)

              val operation = values match {
                case List(operand) => UnaryOp(translateOp(op), assignee(toAssign), operand)
                case List(leftOp, rightOp) => BinaryOp(translateOp(op), assignee(toAssign), leftOp, rightOp)
                case other => rc.reporter.fatalError(s"Unexpected number of arguments for operator $op. Expected 1 or 2 but was ${other.size}")
              }

              (currentBlock <:> operation <:> jump, Nil)
            }

            case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
          }

        cgModule(tree)
    }
}
