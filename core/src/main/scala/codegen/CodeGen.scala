package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import extraction._
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, Neq => IRNeq,
  Eq => IREq, Lt => IRLt, Gt => IRGt, Leq => IRLeq, Geq => IRGeq, Nop => IRNop,
  Plus => IRPlus, Minus => IRMinus, Mul => IRMul, Div => IRDiv,
  BooleanLiteral => IRBooleanLiteral, UnitLiteral => IRUnitLiteral, _}

import codegen.llvm._
import codegen.utils._

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

        def erasedTreeError(t: Tree) = rc.reporter.fatalError(s"This tree should have been erased: $t")

        def filterErasable(t: Tree): Tree = t match {
          case LetIn(_, _, _) |
            MacroTypeDecl(_, _) |
            MacroTypeInst(_, _) |
            ErasableApp(_, _) |
            Refl(_, _) |
            Fold(_, _) |
            Unfold(_, _) |
            UnfoldPositive(_, _) |
            DefFunction(_, _, _, _, _) |  // TODO:
            ErasableLambda(_, _) |
            Abs(_) |
            TypeApp(_, _) |
            Because(_, _) => erasedTreeError(t)

          case _ => t
        }

        def translateOp(op: Operator): Instruction = op match {
          // case Not => acc <:> IRPrim(IRNot, args.map(cgLiteral(_)))
          // case And => acc <:> IRPrim(IRAnd, args.map(cgLiteral(_)))
          // case Or => acc <:> IRPrim(IROr, args.map(cgLiteral(_)))
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

        def cgLiteral(t: Tree): Literal = t match {
          case BooleanLiteral(b) => IRBooleanLiteral(b)
          case NatLiteral(n) => Const(n)
          case UnitLiteral => Const(0)
          case _ => rc.reporter.fatalError(s"This tree isn't a literal: $t")
        }

        def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local])(implicit lh: LocalHandler, m: Module): (Block, List[Instruction]) =
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
              m.add(trueBlock) //trueBlock already contains a jump if it contains a nested if-then-else

              val (falseBlock, falsePhi) = codegen(elze, fBlock, Some(afterBlock.label), Some(falseLocal))
              m.add(falseBlock)

              val parentBlock =
                condPrep <:>
                condPhi <:>
                Branch(Value(condLocal), tBlock.label, fBlock.label)

              m.add(parentBlock)

              val nextPhi =
                truePhi ++
                falsePhi ++
                toAssign.toList.map{
                  case local => Phi(local, List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label)))
                }

              (afterBlock <:> nextPhi <:> Jump(next.get), Nil)
            }

            case BooleanLiteral(b) => if(toAssign.isDefined) {
              if(next.isDefined){
                (block <:> Assign(toAssign.get, Value(IRBooleanLiteral(b))) <:> Jump(next.get), Nil)
              } else {
                (block <:> Assign(toAssign.get, Value(IRBooleanLiteral(b))), Nil)
              }
            } else {
              (block, List(IRBooleanLiteral(b)))
            }

            case Primitive(op, args) => {
              // val argLocals = args.map{
              //   case BooleanLiteral(b) => Left(BooleanLiteral(b))
              //   case NatLiteral(n) => Left(NatLiteral(n))
              //   case Var(v) => Left(Var(v))
              //   case _ => Right(lh.freshLocal())
              // }
              //
              // argLocals.zip(args).map{
              //   case (Left(local), arg) => Left(codegen(arg, block, next, Some(local)))
              //   case (Right(lit), arg) => Right(lit)
              // }

              val argLocals = args.map{
                case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral => None  //Todo replace by isLiteral
                case arg => Some(lh.freshLocal())
              }

              val init: (Block, List[Value]) = (block, Nil)

              val (cB, valueList: List[Value]) = argLocals.zip(args).foldLeft(init) {
                case ((currentBlock, values), (None, arg)) => {
                  (currentBlock, values :+ Value(cgLiteral(arg)))
                }

                case ((currentBlock, values), (Some(local), arg)) => {

                  val tempLabel = lh.freshLabel("tempBlock")
                  val tempBlock = lh.newBlock(tempLabel)

                  val afterLabel = lh.freshLabel("afterBlock")
                  val afterBlock = lh.newBlock(afterLabel)

                  m.add(currentBlock <:> Jump(tempLabel)) //Todo can I do this?

                  val (otherBlock, phi) = codegen(arg, tempBlock, Some(afterLabel), Some(local))
                  m.add(otherBlock)
                  (afterBlock <:> phi, values :+ Value(local))
                }
              }

              val (resultBlock, result) = valueList.tail.foldLeft((cB, valueList.head)){
                case ((cBlock, lhs), rhs) => {
                  val temp = lh.freshLocal()
                  (cBlock <:> BinaryOp(translateOp(op), temp, lhs, rhs), Value(temp))
                }
              }

              val assign = if(toAssign.isDefined){
                List(Assign(toAssign.get, result))
              } else {
                Nil
              }

              val jump = if(next.isDefined){
                List(Jump(next.get))
              } else {
                Nil
              }

              (resultBlock <:> assign <:> jump, Nil)
            }
          }


        //
        // def cgTree(inputTree: Tree, acc: Code, result: Local)(implicit lh: LocalHandler): Code = filterErasable(inputTree) match {
        //     //VariableHandler
        //     case Var(id) => ???
        //     case NatLiteral(n) => ???  //BigInt
        //
        //     case Succ(tree) => ???
        //
        //     case UnitLiteral => ???
        //     case BooleanLiteral(b) => acc <:> Assign(result, IRBooleanLiteral(b))
        //
        //
        //     case IfThenElse(cond, thenn, elze) => {
        //       val conditionLocal = lh.freshLocal("cond")
        //       val condition = cgTree(cond, acc, conditionLocal)
        //       //
        //       // val thenLabel = lh.freshLabel("then") //Should append the name (parentBlock.then)
        //       // val thenLocal = lh.freshLocal("thenLocal")
        //       // val thenBlock = Block.create(thenLabel)
        //       //
        //       // val elseLabel = lh.freshLabel("else")
        //       // val elseLocal = lh.freshLocal("elseLocal")
        //       // val elseBlock = Block.create(elseLabel)
        //       //
        //       // val afterLabel = lh.freshLabel("after")
        //       // val afterBlock = Block.create(elseLabel)
        //       //
        //       // val phi = Phi(result, List((thenLocal, thenLabel), (elseLocal, elseLabel))) //Label should be printed as %label
        //       //
        //       // condition <:> Branch(conditionLocal, thenLabel, elseLabel) <:>
        //       // cgTree(thenn, Code.first(thenBlock), thenLocal) <:> Jump(afterLabel) <:>
        //       // cgTree(elze, Code.first(elseBlock), elseLocal) <:> Jump(afterLabel) <:>
        //       // afterBlock <:> phi
        //
        //       ???
        //     }
        //
        //     //fun of $id = {...}
        //     case Lambda(None, Bind(id, body)) => {
        //       ???
        //     }
        //     case Bind(id, body) => ???
        //
        //     case Lambda(_, _) => rc.reporter.fatalError(s"Unexpected lambda $tree")
        //
        //     //t1.apply(t2)
        //     case App(t1, t2) => ???
        //     case Pair(t1, t2) => ???
        //     case Size(tree) => ???
        //     case First(tree) => ???
        //     case Second(tree) => ???
        //     case Fix(tp, bind) => ???
        //     case NatMatch(t, t1, t2) => ??? //Why only t1 and t2? Recursion? NatMatch(scrut, t1, NatMatch...)
        //     case EitherMatch(t, t1, t2) => ???
        //     case LeftTree(tree) => ???
        //     case RightTree(tree) => ???
        //
        //     case Error(s, tree) => ???
        //
        //     case Primitive(op, args) => {
        //
        //       val locals: List[Local] = args.map(_ => lh.freshLocal())
        //
        //       // val prep = args.zip(locals).map{
        //       //   case (arg, local) => cgTree(arg, acc, local)
        //       // }.reduce(_ <:> _)
        //
        //       val prep = args.zip(locals).foldLeft(acc){
        //         case (prevAcc, (arg, local)) => cgTree(arg, prevAcc, local)
        //       }
        //
        //       val (folding, res) = locals.tail.foldLeft((prep, locals.head)) {
        //         case ((code, lhs), rhs) => {
        //           val temp = lh.freshLocal()
        //           (code <:> BinaryOp(translateOp(op), temp, lhs, rhs), temp)
        //         }
        //       }
        //
        //        folding <:> Assign(result, Variable(res))
        //     }
        //
        //     case BottomType => ???
        //     case TopType => ???
        //     case UnitType => ???
        //     case BoolType => ???
        //     case NatType => ???
        //     case SigmaType(t1, t2) => ???
        //     case SumType(t1, t2) => ???
        //     case PiType(t1, t2) => ???
        //     case IntersectionType(ty, t2) => ???
        //     case RefinementType(t1, t2) => ???
        //     case RecType(n, bind) => ???
        //     case PolyForallType(tree) => ???
        //     case UnionType(t1, t2) => ???
        //     case EqualityType(t1, t2) => ???
        //     case SingletonType(tree) => ???
        //
        //     case _ => rc.reporter.fatalError(s"Code generation not yet implemented for $tree")
        // }

        // def cgLiteral(tree: Tree): Instruction = tree match {
        //   case BooleanLiteral(b) => IRBoolean(b)
        //   case Primitive(op, args) => op match {
        //     case Not => IRPrim(IRNot, args.map(cgLiteral(_)))
        //     case And => IRPrim(IRAnd, args.map(cgLiteral(_)))
        //     case Or => IRPrim(IROr, args.map(cgLiteral(_)))
        //     case _ => rc.reporter.fatalError("Not yet implemented")
        //   }
        // }

        val lh = new LocalHandler(rc)
        // val entryBlock = Block.create(lh.freshLabel("entry"))
        // val entry = Code.first(entryBlock)
        // val body = cgTree(tree, entry, lh.freshLocal("result"))(lh)
        //
        // Module(rc.config.file.getName(), body, Nil)
        val entryBlock = lh.newBlock("entry")
        val module = Module(rc.config.file.getName())
        val end = lh.freshLabel("End")
        val result = lh.freshLocal("result")
        val (block, phi) = codegen(tree, entryBlock, Some(end), Some(result))(lh, module)
        val endBlock = lh.newBlock(end)
        val b = endBlock <:> phi <:> Return(Left(result))
        module.add(block)
        module.add(b)
        module
    }
}
