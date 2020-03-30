package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot,
  BooleanLiteral => IRBoolean, _}
import codegen.llvm._
import codegen.utils._

// General stuff
import org.bytedeco.javacpp._;

// Headers required by LLVM
import org.bytedeco.llvm.LLVM._;
import org.bytedeco.llvm.global.LLVM._;

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
            DefFunction(_, _, _, _, _) |
            ErasableLambda(_, _) |
            Abs(_) |
            TypeApp(_, _) => erasedTreeError(t)

          case _ => t
        }

        def translateOp(op: Operator): Instruction = op match {
          // case Not => acc <:> IRPrim(IRNot, args.map(cgLiteral(_)))
          // case And => acc <:> IRPrim(IRAnd, args.map(cgLiteral(_)))
          // case Or => acc <:> IRPrim(IROr, args.map(cgLiteral(_)))
          case Not => IRNot
          case And => IRAnd
          case Or => IROr

          case Neq => ???
          case Eq => ???
          case Lt => ???
          case Gt => ???
          case Leq => ???
          case Geq => ???

          case Nop => ???

          case Plus => ???
          case Minus => ???
          case Mul => ???
          case Div => ???

          case _ => rc.reporter.fatalError("Not yet implemented")
        }

        def cgTree(inputTree: Tree, acc: Code, result: Local)(implicit lh: LocalHandler): Code = filterErasable(inputTree) match {
            //VariableHandler
            case Var(id) => ???
            case NatLiteral(n) => ???  //BigInt

            case Succ(tree) => ???

            case UnitLiteral => ???
            case BooleanLiteral(b) => acc <:> Assign(result, IRBoolean(b))


            case IfThenElse(cond, thenn, elze) => ???

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

              val locals: List[Local] = args.map(_ => lh.fresh())

              // val prep = args.zip(locals).map{
              //   case (arg, local) => cgTree(arg, acc, local)
              // }.reduce(_ <:> _)

              val prep = args.zip(locals).foldLeft(acc){
                case (prevAcc, (arg, local)) => cgTree(arg, prevAcc, local)
              }

              val (folding, res) = locals.tail.foldLeft((prep, locals.head)) {
                case ((code, lhs), rhs) => {
                  val temp = lh.fresh()
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

            case Because(t1, t2) => ??? //Erased?

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
        val entryBlock = Block.create(lh.freshLabel("entry"))
        val entry = Code.first(entryBlock)
        val body = cgTree(tree, entry, lh.freshLocal("result"))(lh)

        Module(rc.config.file.getName(), body, Nil)
    }
}
