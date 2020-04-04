package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import extraction._
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, Neq => IRNeq,
  Eq => IREq, Lt => IRLt, Gt => IRGt, Leq => IRLeq, Geq => IRGeq, Nop => IRNop,
  Plus => IRPlus, Minus => IRMinus, Mul => IRMul, Div => IRDiv, BooleanLiteral => IRBooleanLiteral, _}
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

        def codegen(inputTree: Tree, code: Code, block: Block, toAssign: Option[Local])(implicit lh: LocalHandler, m: Module): (Block, List[Instruction]) =
          filterErasable(inputTree) match {
            case IfThenElse(cond, thenn, elze) => {

              val trueLocal = lh.freshLocal()
              val (trueBlock, truePhi) = codegen(thenn, code, lh.newBlock("then"), Some(trueLocal))
              m.add(trueBlock)

              val falseLocal = lh.freshLocal()
              val (falseBlock, falsePhi) = codegen(thenn, code, lh.newBlock("else"), Some(falseLocal))
              m.add(falseBlock)

              val condLocal = lh.freshLocal()
              val (condPrep, condPhi) = codegen(cond, code, block, Some(condLocal))

              val parentBlock =
                condPrep <:>
                condPhi <:>
                Branch(condLocal, trueBlock.label, falseBlock.label)

              val nextPhi =
                truePhi ++
                falsePhi ++
                toAssign.toList.map{
                  case local => Phi(local, List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label)))
                }

              (parentBlock, nextPhi)
            }

            case BooleanLiteral(b) => if(toAssign.isDefined) {
              (block, List(Assign(toAssign.get, IRBooleanLiteral(b))))
            } else {
              (block, List(IRBooleanLiteral(b)))
            }

            case Primitive(op, args) => {

              ???
            }
          }



        def cgTree(inputTree: Tree, acc: Code, result: Local)(implicit lh: LocalHandler): Code = filterErasable(inputTree) match {
            //VariableHandler
            case Var(id) => ???
            case NatLiteral(n) => ???  //BigInt

            case Succ(tree) => ???

            case UnitLiteral => ???
            case BooleanLiteral(b) => acc <:> Assign(result, IRBooleanLiteral(b))


            case IfThenElse(cond, thenn, elze) => {
              val conditionLocal = lh.freshLocal("cond")
              val condition = cgTree(cond, acc, conditionLocal)
              //
              // val thenLabel = lh.freshLabel("then") //Should append the name (parentBlock.then)
              // val thenLocal = lh.freshLocal("thenLocal")
              // val thenBlock = Block.create(thenLabel)
              //
              // val elseLabel = lh.freshLabel("else")
              // val elseLocal = lh.freshLocal("elseLocal")
              // val elseBlock = Block.create(elseLabel)
              //
              // val afterLabel = lh.freshLabel("after")
              // val afterBlock = Block.create(elseLabel)
              //
              // val phi = Phi(result, List((thenLocal, thenLabel), (elseLocal, elseLabel))) //Label should be printed as %label
              //
              // condition <:> Branch(conditionLocal, thenLabel, elseLabel) <:>
              // cgTree(thenn, Code.first(thenBlock), thenLocal) <:> Jump(afterLabel) <:>
              // cgTree(elze, Code.first(elseBlock), elseLocal) <:> Jump(afterLabel) <:>
              // afterBlock <:> phi

              ???
            }

            //fun of $id = {...}
            case Lambda(None, Bind(id, body)) => {
              ???
            }
            case Bind(id, body) => ???

            case Lambda(_, _) => rc.reporter.fatalError(s"Unexpected lambda $tree")

            //t1.apply(t2)
            case App(t1, t2) => ???
            case Pair(t1, t2) => ???
            case Size(tree) => ???
            case First(tree) => ???
            case Second(tree) => ???
            case Fix(tp, bind) => ???
            case NatMatch(t, t1, t2) => ??? //Why only t1 and t2? Recursion? NatMatch(scrut, t1, NatMatch...)
            case EitherMatch(t, t1, t2) => ???
            case LeftTree(tree) => ???
            case RightTree(tree) => ???

            case Error(s, tree) => ???

            case Primitive(op, args) => {

              val locals: List[Local] = args.map(_ => lh.freshLocal())

              // val prep = args.zip(locals).map{
              //   case (arg, local) => cgTree(arg, acc, local)
              // }.reduce(_ <:> _)

              val prep = args.zip(locals).foldLeft(acc){
                case (prevAcc, (arg, local)) => cgTree(arg, prevAcc, local)
              }

              val (folding, res) = locals.tail.foldLeft((prep, locals.head)) {
                case ((code, lhs), rhs) => {
                  val temp = lh.freshLocal()
                  (code <:> BinaryOp(translateOp(op), temp, lhs, rhs), temp)
                }
              }

               folding <:> Assign(result, Variable(res))
            }

            case BottomType => ???
            case TopType => ???
            case UnitType => ???
            case BoolType => ???
            case NatType => ???
            case SigmaType(t1, t2) => ???
            case SumType(t1, t2) => ???
            case PiType(t1, t2) => ???
            case IntersectionType(ty, t2) => ???
            case RefinementType(t1, t2) => ???
            case RecType(n, bind) => ???
            case PolyForallType(tree) => ???
            case UnionType(t1, t2) => ???
            case EqualityType(t1, t2) => ???
            case SingletonType(tree) => ???

            case _ => rc.reporter.fatalError(s"Code generation not yet implemented for $tree")
        }

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

        val result = lh.freshLocal("result")
        val (block, phi) = codegen(tree, Code.empty, entryBlock, Some(result))(lh, module)

        val b = block <:> phi <:> Return(Left(result))
        module.add(b)
        module
    }
}
