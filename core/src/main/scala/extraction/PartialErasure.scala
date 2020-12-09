package fit
package core
package extraction

import codegen.CodeGen
import parser.FitParser
import trees._
import util.RunContext

class PartialErasure(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (PartialErasure.erase(t, true), ())
}

object PartialErasure {
  def erase(t: Tree, topLevel: Boolean = false)(implicit rc: RunContext): Tree = t match {
    case Var(_) => t
    case UnitLiteral => t
    case NatLiteral(_) => t
    case BooleanLiteral(_) => t
    case Refl(_, _) => UnitLiteral
    case IfThenElse(cond, t1, t2) => IfThenElse(erase(cond), erase(t1), erase(t2))
    case App(t1, t2) => App(erase(t1), erase(t2))
    case Pair(t1, t2) => Pair(erase(t1), erase(t2))
    case Size(t) => Size(erase(t))
    case Succ(t) => Succ(erase(t))
    case First(t) => First(erase(t))
    case Second(t) => Second(erase(t))
    case LeftTree(t) => LeftTree(erase(t))
    case RightTree(t) => RightTree(erase(t))
    case Because(t1, t2) => erase(t1)
    case Bind(id2, e) => Bind(id2, erase(e, topLevel))
    case Lambda(tpe, bind) => Lambda(tpe, erase(bind))
    case ErasableLambda(_, Bind(id, body)) => erase(body)

    case Fix(tpe, bind) => bind match {
      case TreeBuilders.Binds(_, tree) => erase(tree)
    }

    case LetIn(tpe, t1, bind) => LetIn(tpe, erase(t1), erase(bind))
    case MacroTypeDecl(tpe, Bind(id, body)) => erase(body)

    case NatMatch(n, e1, Bind(id, e2)) => {
      val scrut= Identifier.fresh("nat_scrut")
      val cond = Primitive(Eq, List(Var(scrut), NatLiteral(BigInt(0))))
      val decrement = Primitive(Minus, List(Var(scrut), NatLiteral(BigInt(1))))

      val rec = IfThenElse(cond, e1, e2.replace(id, decrement))
      erase(LetIn(Some(NatType), n, Bind(scrut, rec)))
    }

    case EitherMatch(t, bind1, bind2) => EitherMatch(erase(t), erase(bind1), erase(bind2))
    case Primitive(op, args) => Primitive(op, args.map(erase(_)))
    case ErasableApp(t1, _) => erase(t1)
    case Fold(_, t) => erase(t)
    case Unfold(t1, bind) => erase(LetIn(None, t1, bind))
    case UnfoldPositive(t1, bind) => erase(LetIn(None, t1, bind))
    case Abs(Bind(id, body)) => erase(body)
    case TypeApp(t1, _) => erase(t1)
    case Error(s, optType) => Error(s, optType)

    case _ => rc.reporter.fatalError(s"Partial Erasure is not implemented on $t (${t.getClass}).")
  }
}
