package stainlessfit
package core
package interpreter

import trees._
import util.RunContext
import parser.FitParser

object Interpreter {

  val zero = BigInt(0)

  def smallStep(e: Tree)(implicit rc: RunContext): Tree = {
    e match {
      case IfThenElse(BooleanLiteral(true), t1, t2) => t1
      case IfThenElse(BooleanLiteral(false), t1, t2) => t2
      case IfThenElse(t, tt, tf) => IfThenElse(smallStep(t), tt, tf)

      case Pair(t1, t2) if t1.isValue => Pair(t1, smallStep(t2))
      case Pair(t1, t2) => Pair(smallStep(t1), t2)

      case First(Pair(t1, t2)) => t1
      case First(t) => First(smallStep(t))

      case Second(Pair(t1, t2)) => t2
      case Second(t) => Second(smallStep(t))

      case App(Lambda(_, bind), v) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case App(Lambda(tp, bind: Bind), t) => App(Lambda(tp, bind), smallStep(t))
      case App(f, v) => App(smallStep(f), v)
      case Fix(_, Bind(id, bind)) if bind.isBind => Tree.replaceBind(bind, e)

      case NatMatch(NatLiteral(`zero`), t0, _) => t0
      case NatMatch(NatLiteral(n), _, bind) if bind.isBind => Tree.replaceBind(bind, NatLiteral(n - 1))
      case NatMatch(t, t0, bind) => NatMatch(smallStep(t), t0, bind)

      case EitherMatch(LeftTree(v), bind, _) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case EitherMatch(RightTree(v), _, bind) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case EitherMatch(t, b1, b2) => EitherMatch(smallStep(t), b1, b2)

      case Primitive(Not, BooleanLiteral(b) :: Nil) => BooleanLiteral(!b)
      case Primitive(And, BooleanLiteral(b1) :: BooleanLiteral(b2) :: Nil) => BooleanLiteral(b1 && b2)
      case Primitive(Or, BooleanLiteral(b1) :: BooleanLiteral(b2) :: Nil) => BooleanLiteral(b1 || b2)

      case Primitive(Neq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 != n2)
      case Primitive(Eq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 == n2)
      case Primitive(Lt, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 < n2)
      case Primitive(Gt, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 > n2)
      case Primitive(Leq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 <= n2)
      case Primitive(Geq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 >= n2)

      case Primitive(Plus, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => NatLiteral(n1 + n2)
      case Primitive(Minus, NatLiteral(n1) :: NatLiteral(n2) :: Nil) if n1 >= n2 => NatLiteral(n1 - n2)
      case Primitive(Mul, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => NatLiteral(n1 * n2)
      case Primitive(Div, NatLiteral(n1) :: NatLiteral(n2) :: Nil) if n2 != 0 => NatLiteral(n1 / n2)

      case Primitive(p, x :: Nil) if !x.isValue => Primitive(p, smallStep(x) :: Nil)
      case Primitive(p, x :: y :: Nil) if !x.isValue => Primitive(p, smallStep(x) :: y :: Nil)
      case Primitive(p, x :: y :: Nil) if !y.isValue => Primitive(p, x :: smallStep(y) :: Nil)

      case LeftTree(e) => LeftTree(smallStep(e))
      case RightTree(e) => RightTree(smallStep(e))

      case Error(msg, _) => Error(msg, None)

      case _ =>
        rc.reporter.fatalError(s"Evaluation is stuck on: $e")
    }
  }

  def evaluate(e: Tree)(implicit rc: RunContext): Tree = e match {
    case Error(_, _) => e
    case tree if tree.isValue => tree
    case _ => evaluate(smallStep(e))
  }
}
