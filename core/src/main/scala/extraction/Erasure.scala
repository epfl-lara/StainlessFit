package stainlessfit
package core
package extraction

import util.RunContext
import parser.FitParser
import trees._

class Erasure(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (Erasure.erase(t), ())
}

object Erasure {
  def erase(t: Tree)(implicit rc: RunContext): Tree = t match {
    case Var(_) => t
    case UnitLiteral => t
    case NatLiteral(_) => t
    case BooleanLiteral(_) => t
    case Refl(_, _) => UnitLiteral
    case IfThenElse(cond, t1, t2) => IfThenElse(erase(cond), erase(t1), erase(t2))
    case App(t1, t2) => App(erase(t1), erase(t2))
    case Pair(t1, t2) => Pair(erase(t1), erase(t2))
    case Size(t) => Size(erase(t))
    case First(t) => First(erase(t))
    case Second(t) => Second(erase(t))
    case LeftTree(t) => LeftTree(erase(t))
    case RightTree(t) => RightTree(erase(t))
    case Because(t1, t2) => erase(t1)
    case Bind(id2, e) => Bind(id2, erase(e))
    case Lambda(_, bind) => Lambda(None, erase(bind))
    case ErasableLambda(_, Bind(id, body)) => erase(body)
    case Fix(_, bind) => Fix(None, erase(bind))
    case LetIn(_, t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case MacroTypeDecl(tpe, Bind(id, body)) => erase(body)
    case NatMatch(t, t0, bind) => NatMatch(erase(t), erase(t0), erase(bind))
    case EitherMatch(t, bind1, bind2) => EitherMatch(erase(t), erase(bind1), erase(bind2))
    case Primitive(op, args) => Primitive(op, args.map(erase(_)))
    case ErasableApp(t1, _) => erase(t1)
    case Fold(_, t) => erase(t)
    case Unfold(t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case UnfoldPositive(t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case Abs(Bind(id, body)) => erase(body)
    case TypeApp(t1, _) => erase(t1)
    case Error(s, _) => Error(s, None)
    case _ => rc.reporter.fatalError(s"Erasure is not implemented on $t (${t.getClass}).")
  }
}
