package stainlessfit
package core
package interpreter

import trees._
import util.RunContext
import parser.FitParser
import typechecker.Context
import typechecker.ScalaDepSugar._

object Interpreter {
  val zero = BigInt(0)

  def evaluateWithContext(c: Context, e: Tree)(implicit rc: RunContext): Tree = {
    e match {
      // case IfThenElse(BooleanLiteral(true), t1, t2) => t1
      // case IfThenElse(BooleanLiteral(false), t1, t2) => t2
      // case IfThenElse(t, tt, tf) => IfThenElse(evaluateWithContext(c, t), tt, tf)

      case Var(id) => c.termVariables(id) match {
        case SingletonType(_, t) => evaluateWithContext(c, t)
        case _ => e
      }

      case Pair(t1, t2) => Pair(evaluateWithContext(c, t1), evaluateWithContext(c, t2))

      case First(t) => evaluateWithContext(c, t) match {
        case Pair(t1, t2) => t1
        case e => e
      }

      case Second(t) => evaluateWithContext(c, t) match {
        case Pair(t1, t2) => t2
        case e => e
      }

      case App(f, t) =>
        val nt = evaluateWithContext(c, t)
        evaluateWithContext(c, f) match {
          case Lambda(_, Bind(id, body)) => evaluateWithContext(c, body.replace(id, nt))
          case nf => App(nf, nt)
        }

      case LetIn(_, value, Bind(id, body)) =>
        val nvalue = evaluateWithContext(c, value)
        val nbody = body.replace(id, nvalue)
        evaluateWithContext(c, nbody)

      case NatMatch(t, t1, b2 @ Bind(id2, t2)) =>
        evaluateWithContext(c, t) match {
          case NatLiteral(`zero`) => evaluateWithContext(c, t1)
          case NatLiteral(n) => evaluateWithContext(c, t2.replace(id2, NatLiteral(n - 1)))
          case nt => NatMatch(nt, t1, b2)
        }

      case EitherMatch(t, b1@Bind(id1, t1), b2@Bind(id2, t2)) =>
        evaluateWithContext(c, t) match {
          case LeftTree(e1) => evaluateWithContext(c, t1.replace(id1, e1))
          case RightTree(e2) => evaluateWithContext(c, t2.replace(id2, e2))
          case nt => EitherMatch(nt, b1, b2)
        }

      case ListMatch(t, t1, b2 @ Bind(idHead, Bind(idTail, t2))) =>
        evaluateWithContext(c, t) match {
          case LNil() => evaluateWithContext(c, t1)
          case LCons(tHead, tTail) => evaluateWithContext(c, t2.replace(idHead, tHead).replace(idTail, tTail))
          case nt => ListMatch(nt, t1, b2)
        }

      // case Primitive(Not, BooleanLiteral(b) :: Nil) => BooleanLiteral(!b)
      // case Primitive(And, BooleanLiteral(b1) :: BooleanLiteral(b2) :: Nil) => BooleanLiteral(b1 && b2)
      // case Primitive(Or, BooleanLiteral(b1) :: BooleanLiteral(b2) :: Nil) => BooleanLiteral(b1 || b2)

      // case Primitive(Neq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 != n2)
      // case Primitive(Eq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 == n2)
      // case Primitive(Lt, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 < n2)
      // case Primitive(Gt, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 > n2)
      // case Primitive(Leq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 <= n2)
      // case Primitive(Geq, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => BooleanLiteral(n1 >= n2)

      // case Primitive(Plus, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => NatLiteral(n1 + n2)
      // case Primitive(Minus, NatLiteral(n1) :: NatLiteral(n2) :: Nil) if n1 >= n2 => NatLiteral(n1 - n2)
      // case Primitive(Mul, NatLiteral(n1) :: NatLiteral(n2) :: Nil) => NatLiteral(n1 * n2)
      // case Primitive(Div, NatLiteral(n1) :: NatLiteral(n2) :: Nil) if n2 != 0 => NatLiteral(n1 / n2)

      // case Primitive(p, x :: Nil) if !x.isValue => Primitive(p, evaluateWithContext(c, x) :: Nil)
      // case Primitive(p, x :: y :: Nil) if !x.isValue => Primitive(p, evaluateWithContext(c, x) :: y :: Nil)
      // case Primitive(p, x :: y :: Nil) if !y.isValue => Primitive(p, x :: evaluateWithContext(c, y) :: Nil)

      case LeftTree(e) => LeftTree(evaluateWithContext(c, e))
      case RightTree(e) => RightTree(evaluateWithContext(c, e))

      case FixWithDefault(_, t, td, 0) =>
        evaluateWithContext(c, td)
      case FixWithDefault(ty, t @ Bind(id, tBody), td, depthFuel) =>
        val newFixD = FixWithDefault(ty, t, td, depthFuel - 1)
        evaluateWithContext(c, tBody.replace(id, newFixD))

      case _ => e
    }
  }

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

      case _ =>
        rc.reporter.fatalError(s"Evaluation is stuck on: $e")
    }
  }

  def evaluate(e: Tree)(implicit rc: RunContext): Tree = {
    if (e.isValue) e
    else evaluate(smallStep(e))
  }
}
