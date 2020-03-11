package stainlessfit
package core
package partialEvaluator

import trees._
import util.RunContext
import parser.FitParser

object PartialEvaluator {



  def partEval(t: Tree)(implicit rc: RunContext, vars: Map[Identifier,Tree]): Tree = {
    t match {
      case Var(id) => vars.getOrElse(id,t)
      case UnitLiteral => t
      case NatLiteral(_) => t
      case BooleanLiteral(_) => t
      case IfThenElse(cond, t1, t2) => 
        val condEval = partEval(cond)
        condEval match{
          case BooleanLiteral(true) =>
            partEval(t1)
          case BooleanLiteral(false) =>
            partEval(t2)
          case _ =>
            IfThenElse(condEval,partEval(t1),partEval(t2))
        }
      case App(t1, t2) => ???
      case First(t) => 
        val eval = partEval(t)
        eval match{
          case Pair(t1,t2) => partEval(t1)
          case _ => First(eval)
        }
      case Second(t) => 
        val eval = partEval(t)
        eval match{
          case Pair(t1,t2) => partEval(t2)
          case _ => Second(eval)
        }
      case Pair(t1, t2) => Pair(partEval(t1),partEval(t2))
      case Size(t) => ???
      case LeftTree(t) => ???
      case RightTree(t) => ???
      case Because(t1, t2) => ???
      case Bind(id2, e) => ???
      case Lambda(None, bind) => ???
      case Lambda(Some(tp), bind) => ???
      case ErasableLambda(tp, bind) => ???
      case Fix(None, bind) => ???
      case Fix(Some(tp), bind) => ???
      case LetIn(None, v1, bind) => ???
      case LetIn(Some(tp), v1, bind) => ???
      case MacroTypeDecl(tpe, bind) => ???
      case MacroTypeInst(v1, args) => ???
      case NatMatch(t, t0, bind) => ???
      case EitherMatch(t, bind1, bind2) => ???
      case Primitive(op, args) => ???
      case ErasableApp(t1, t2) => ???
      case Fold(tp, t) => ???
      case Unfold(t, bind) => ???
      case UnfoldPositive(t, bind) => ???
      case Abs(bind) => ???
      case TypeApp(abs, t) => ???
      case Error(_, _) => ???
      case NatType => ???
      case BoolType => ???
      case UnitType => ???
      case SumType(t1, t2) => ???
      case PiType(t1, bind) => ???
      case SigmaType(t1, bind) => ???
      case IntersectionType(t1, bind) => ???
      case RefinementType(t1, bind) => ???
      case RecType(n, bind) => ???
      case PolyForallType(bind) => ???

      case BottomType => t
      case TopType => t

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $t (${t.getClass}).")
    }
  }
}