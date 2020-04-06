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

// General stuff
import org.bytedeco.javacpp._;

// Headers required by LLVM
import org.bytedeco.llvm.LLVM._;
import org.bytedeco.llvm.global.LLVM._;

class CodeGen(implicit val rc: RunContext) extends Phase[Module] {
  def transform(t: Tree): (Tree, Module) = (t, CodeGen.genLLVM(t, true))
}

object CodeGen {
    def genLLVM(tree: Tree, isMain: Boolean)(implicit rc: RunContext): Module = {

        def cgDefFunction(defFun: DefFunction): Function = {
          val DefFunction(args, optReturnType, _, bind, _) = defFun

          val params = args.toList.map{
            case TypedArgument(id, tpe) => (id, ParamDef(translateType(tpe), Local(id.name)))
            case arg => rc.reporter.fatalError(s"Unexpected type for arg $arg")
          }

          val (fname, body) = extractBody(bind)

          val returnType = translateType(optReturnType.get)
          cgFunction(returnType, Global(fname.name), params, body)
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

        def extractBody(bind: Tree): (Identifier, Tree) = bind match {
          case Bind(id, rec: Bind) => extractBody(rec)
          case Bind(id, body) => (id, body)
          case _ => rc.reporter.fatalError(s"Couldn't find the body in $bind")
        }

        def extractDefFun(t: Tree): (List[DefFunction], Tree) = t match {
          case defFun @ DefFunction(_, _, _, _, otherDefs: DefFunction) => {
            val (defs, rest) = extractDefFun(otherDefs)
            (defFun +: defs, rest)
          }
          case defFun @ DefFunction(_, _, _, _, rest) => (List(defFun), rest)
          case _ => rc.reporter.fatalError(s"Couldn't find the body in $t")
        }

        def cgModule(inputTree: Tree): Module = {
          val lh = new LocalHandler(rc)

          val (functions, bind) = extractDefFun(inputTree)

          val funs = functions map cgDefFunction

          val (id, body) = extractBody(bind)

          val returnType = resultType(body)(lh) match {
            case FunctionReturnType(funName) => funs.filter(fun => fun.name == funName).head.returnType
            case otherType => otherType
          }
          val main = cgFunction(returnType, Global("main"), Nil, body)  //Might be a function call

          val module = Module(
            rc.config.file.getName(),
            main,
            funs
          )

          module
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

        def cgLiteral(t: Tree)(implicit lh: LocalHandler): Value = t match {
          case BooleanLiteral(b) => Value(IRBooleanLiteral(b))
          case NatLiteral(n) => Value(Nat(n))
          case UnitLiteral => Value(Nat(0))
          case Var(id) => Value(lh.getLocal(id))
          case _ => rc.reporter.fatalError(s"This tree isn't a literal: $t")
        }

        def cgValue(tpe: Type, value: Value, next: Option[Label], toAssign: Option[Local]): List[Instruction] = {
          val assign = toAssign.toList.map(local => Assign(local, tpe, value))
          val jump = next.toList.map(label => Jump(label))

          if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")

          assign ++ jump
        }

        def flattenPrimitive(t: Tree): List[Tree] = t match {
          case Primitive(op, args) => args.flatMap{
            case Primitive(op2, args2) if op2 == op => flattenPrimitive(Primitive(op2, args2))
            case other => List(other)
          }

          case _ => rc.reporter.fatalError(s"flattenPrimitive is not defined for $t")
        }

        def translateType(tpe: Tree): Type = tpe match {
          case BoolType => BooleanType
          case NatType => IRNatType
          case UnitType => IRUnitType
          case Bind(_, rest) => translateType(rest)
          case _ => rc.reporter.fatalError(s"Unkown type $tpe")
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

        def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
          (implicit lh: LocalHandler, f: Function): (Block, List[Instruction]) =
          filterErasable(inputTree) match {
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
                toAssign.toList.map{
                  case local => Phi(local, resultType(thenn), List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label)))
                } //Need a better way to check for the type

              (afterBlock <:> nextPhi <:> Jump(next.get), Nil)
            }

            case BooleanLiteral(b) => {
              // val assign = toAssign.toList.map(local => Assign(local, BooleanType, Value(IRBooleanLiteral(b))))
              // val jump = next.toList.map(label => Jump(label))
              //
              // if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")
              //
              // (block <:> assign <:> jump, Nil)
              (block <:> cgValue(BooleanType, Value(IRBooleanLiteral(b)), next, toAssign), Nil)
            }

            case NatLiteral(n) => {
              // val assign = toAssign.toList.map(local => Assign(local, IRNatType, Value(Nat(n))))
              // val jump = next.toList.map(label => Jump(label))
              //
              // if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")
              //
              // (block <:> assign <:> jump, Nil)
              (block <:> cgValue(IRNatType, Value(Nat(n)), next, toAssign), Nil)
            }

            case Primitive(op, args) => {

              val flatArgs = flattenPrimitive(inputTree)
              val (cB, valueList) = cgIntermediateBlocks(flatArgs, block)
              // val argLocals = flatArgs.map{
              //   case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral | Var(_) => None  //Todo replace by isLiteral
              //   case arg => Some(lh.freshLocal())
              // }
              //
              // val init: (Block, List[Value]) = (block, Nil)
              //
              // val (cB, valueList: List[Value]) = argLocals.zip(flatArgs).foldLeft(init) {
              //   case ((currentBlock, values), (None, arg)) => {
              //     (currentBlock, values :+ Value(cgLiteral(arg)))
              //   }
              //
              //   case ((currentBlock, values), (Some(local), arg)) => {
              //     //TODO check if an intermediate block is necessary
              //     val tempLabel = lh.freshLabel("tempBlock")
              //     val tempBlock = lh.newBlock(tempLabel)
              //
              //     val afterLabel = lh.freshLabel("afterBlock")
              //     val afterBlock = lh.newBlock(afterLabel)
              //
              //     f.add(currentBlock <:> Jump(tempLabel)) //Todo can I do this?
              //
              //     val (otherBlock, phi) = codegen(arg, tempBlock, Some(afterLabel), Some(local))
              //     f.add(otherBlock)
              //     (afterBlock <:> phi, values :+ Value(local))
              //   }
              // }

              val last = valueList.size - 1
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
              // val assign = if(toAssign.isDefined){
              //   //List(Assign(toAssign.get, result))
              // } else {
              //   Nil
              // }
            }

            case Var(id) => {
              // val assign = toAssign.toList.map(local => Assign(local, lh.getType(id), Value(lh.getLocal(id))))
              // val jump = next.toList.map(label => Jump(label))
              //
              // if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")
              //
              // (block <:> assign <:> jump, Nil)
              (block <:> cgValue(lh.getType(id), Value(lh.getLocal(id)), next, toAssign), Nil)
            }

            case call @ App(_, _) => cgFunctionCall(call, block, next, toAssign)

            case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
          }

          def cgIntermediateBlocks(flatArgs: List[Tree], initialBlock: Block)(implicit lh: LocalHandler, f: Function): (Block, List[Value]) = {

            val argLocals = flatArgs.map{
              case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral | Var(_) => None  //Todo replace by isLiteral
              case arg => Some(lh.freshLocal())
            }

            val init: (Block, List[Value]) = (initialBlock, Nil)

            val (cB, valueList: List[Value]) = argLocals.zip(flatArgs).foldLeft(init) {
              case ((currentBlock, values), (None, arg)) => {
                (currentBlock, values :+ cgLiteral(arg))
              }

              case ((currentBlock, values), (Some(local), arg)) => {
                //TODO check if an intermediate block is necessary
                val tempLabel = lh.freshLabel("tempBlock")
                val tempBlock = lh.newBlock(tempLabel)

                val afterLabel = lh.freshLabel("afterBlock")
                val afterBlock = lh.newBlock(afterLabel)

                f.add(currentBlock <:> Jump(tempLabel)) //Todo can I do this?

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


          //     call match {
          //   case App(Var(funId), args) => { //base case
          //     val flatArgs = flattenParams(args)
          //     val (cB, valueList) = cgIntermediateBlocks(flatArgs, block)
          //
          //     val result = toAssign.getOrElse(lh.freshLocal("unused"))
          //
          //     val jump = next.toList.map(label => Jump(label))
          //     (cB <:> Call(result, Global(funId.name), valueList) <:> jump, Nil)
          //   }
          //
          //   case App(App(_, _), _) => {
          //
          //   }
          //   case _ => rc.reporter.fatalError(s"Unable to apply $call yet")
          // }


          def flattenParams(t: Tree): List[Tree] = t match {
            //TODO might be able to integrate into flattenPrimitive
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

        cgModule(tree)
    }
}
