package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, BooleanLiteral => IRBoolean, Primitive => IRPrim, _}
import codegen.llvm._
import codegen.utils._

// General stuff
import org.bytedeco.javacpp._;

// Headers required by LLVM
import org.bytedeco.llvm.LLVM._;
import org.bytedeco.llvm.global.LLVM._;

object CodeGen {
    def genLLVM(tree: Tree, isMain: Boolean)(implicit rc: RunContext): Module = {

        def cgTree(tree: Tree, acc: Code)(implicit lh: LocalHandler): Code = tree match {
            //VariableHandler
            case Var(id) => ???
            case NatLiteral(n) => ???  //BigInt

            case Succ(tree) => ???

            case UnitLiteral => ???
            case BooleanLiteral(b) => acc <:> IRBoolean(b)

            case Bind(id, body) => ???

            case IfThenElse(cond, thenn, elze) => ???

            case Lambda(tp, bind) => ???  //tp = type parameter?
            case DefFunction(args, optRet, optMeasure, body, rest) => ???
            //You can create function in the middle of the code?
            case ErasableLambda(ty, bind) => ???
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

            case LetIn(tp, value, body) => ???
            case MacroTypeDecl(tp, body) => ???
            case MacroTypeInst(v, args) => ???

            case Error(s, tree) => ???
            case Primitive(op, args) => op match {
              case Not => acc <:> IRPrim(IRNot, args.map(cgLiteral(_)))
              case And => acc <:> IRPrim(IRAnd, args.map(cgLiteral(_)))
              case Or => acc <:> IRPrim(IROr, args.map(cgLiteral(_)))

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

            case ErasableApp(t1, t2) => ???
            case Refl(t1, t2) => ???
            case Fold(tp, tree) => ???
            case Unfold(tree, bind) => ???
            case UnfoldPositive(tree, bind) => ???

            case Abs(tree) => ???

            case TypeApp(t1, t2) => ???
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
            case Because(t1, t2) => ???

            case _ => rc.reporter.fatalError(s"Code generation not yet implemented for $tree")
        }

        def cgLiteral(tree: Tree): Instruction = tree match {
          case BooleanLiteral(b) => IRBoolean(b)
          case Primitive(op, args) => op match {
            case Not => IRPrim(IRNot, args.map(cgLiteral(_)))
            case And => IRPrim(IRAnd, args.map(cgLiteral(_)))
            case Or => IRPrim(IROr, args.map(cgLiteral(_)))
            case _ => rc.reporter.fatalError("Not yet implemented")
          }
        }

        val lh = new LocalHandler(rc)
        val entry = Code(Nil, Block(lh.freshLabel("entry"), Nil))
        val body = cgTree(tree, entry)(lh)

        Module(rc.config.file.getName(), body, Nil)
    }
}
