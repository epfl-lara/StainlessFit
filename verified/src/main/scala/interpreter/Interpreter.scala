package interpreter

import _root_.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

object Interpreter {

  def isValue(e: Tree): Boolean = e match {
    case BottomTree => true
    case UnitLiteral => true
    case NatLiteral(_) => true
    case BoolLiteral(_) => true
    case Var(_, _) => true
    case Lambda(_, _) => true
    case Pair(t1, t2) => isValue(t1) && isValue(t2)
    case RightTree(t) => isValue(t)
    case LeftTree(t) => isValue(t)
    case _ => false
  }

  def replace(xvar: Var, v: Tree, body: Tree): Tree = {
    decreases(body)
    body match {
      case BottomTree => body
      case UnitLiteral => body
      case NatLiteral(n) => body
      case BoolLiteral(b) => body
      case Var(id, y) if Var(id, y) == xvar => v
      case Var(id1, y) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(replace(xvar, v, cond), replace(xvar, v, t1), replace(xvar, v, t2))
      case App(t1, t2) =>
        App(replace(xvar, v, t1), replace(xvar, v, t2))
      case Pair(t1, t2) => Pair(replace(xvar, v, t1), replace(xvar, v, t2))
      case First(t) => First(replace(xvar, v, t))
      case Second(t) => Second(replace(xvar, v, t))
      case LeftTree(t) => LeftTree(replace(xvar, v, t))
      case RightTree(t) => RightTree(replace(xvar, v, t))
      case Because(t1, t2) => Because(replace(xvar, v, t1), replace(xvar, v, t2))
      case Bind(Some(yvar), e) if (xvar == yvar) => body
      case Bind(yvar, e) => Bind(yvar, replace(xvar, v, e))

      case Lambda(tp, bind) => replace(xvar, v, bind) match {
        case b: Bind => Lambda(tp, b)
        case _ => BottomTree
      }
      case Fix(bind) => replace(xvar, v, bind) match {
        case b: Bind => Fix(b)
        case _ => BottomTree
      }
      case LetIn(tp, v1, bind) => replace(xvar, v, bind) match {
        case b: Bind => LetIn(tp, replace(xvar, v, v1), b)
        case _ => BottomTree
      }
      case Match(t, t0, bind) => replace(xvar, v, bind) match {
        case b: Bind => Match(replace(xvar, v, t), replace(xvar, v, t0), b)
        case _ => BottomTree
      }
      case EitherMatch(t, bind1, bind2) => (replace(xvar, v, bind1), replace(xvar, v, bind2)) match {
        case (b1: Bind, b2: Bind) => EitherMatch(replace(xvar, v, t), b1, b2)
        case _ => BottomTree
      }

      case Primitive(op, args) => Primitive(op, args.map(replace(xvar, v, _)))
      case _ => body
    }
  }

  def replaceBind(bind: Bind, v: Tree): Tree = {
    bind match {
      case Bind(None(), body) => body
      case Bind(Some(xvar: Var), body) => replace(xvar, v, body)
    }
  }

  def smallStep(e: Tree): Tree = {
    decreases(e)
    e match {
      case IfThenElse(BoolLiteral(true), t1, t2) => t1
      case IfThenElse(BoolLiteral(false), t1, t2) => t2
      case IfThenElse(t, _, _) if isValue(t) => BottomTree
      case IfThenElse(t, tt, tf) => IfThenElse(smallStep(t), tt, tf)

      case App(Lambda(_, bind: Bind), v) if isValue(v) => replaceBind(bind, v)
      case App(Lambda(tp, bind: Bind), t) => App(Lambda(tp, bind), smallStep(t))
      case App(f, _) if isValue(f) => BottomTree /* f is a value and not a lambda */
      case App(f, v) => App(smallStep(f), v)

      case Pair(t1, t2) if isValue(t1) => Pair(t1, smallStep(t2))
      case Pair(t1, t2) => Pair(smallStep(t1), t2)

      case First(Pair(t1, t2)) => t1
      case First(t) if isValue(t) => BottomTree
      case First(t) => First(smallStep(t))

      case Second(Pair(t1, t2)) => t2
      case Second(t) if isValue(t) => BottomTree
      case Second(t) => Second(smallStep(t))

      case Fix(bind: Bind) => replaceBind(bind, Lambda(None(), Bind(None(), e)))

      case Match(NatLiteral(BigInt(0)), t0, _) => t0
      case Match(NatLiteral(n), _, bind: Bind) => replaceBind(bind, NatLiteral(n - 1))
      case Match(t, _, _) if isValue(t) => BottomTree
      case Match(t, t0, bind: Bind) => Match(smallStep(t), t0, bind)

      case EitherMatch(LeftTree(v), bind: Bind, _) => replaceBind(bind, v)
      case EitherMatch(RightTree(v), _, bind: Bind) => replaceBind(bind, v)
      case EitherMatch(t, _, _) if isValue(t) => BottomTree
      case EitherMatch(t, b1: Bind, b2: Bind) => EitherMatch(smallStep(t), b1, b2)

      case LetIn(tp, v, bind: Bind) => replaceBind(bind, v)

      case Primitive(Not, BoolLiteral(b)::Nil()) => BoolLiteral(!b)

      case Primitive(And, BoolLiteral(b1)::BoolLiteral(b2)::Nil()) => BoolLiteral(b1 && b2)
      case Primitive(Or, BoolLiteral(b1)::BoolLiteral(b2)::Nil()) => BoolLiteral(b1 || b2)
      case Primitive(Neq, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 != b2)
      case Primitive(Eq, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 == b2)
      case Primitive(Lt, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 < b2)
      case Primitive(Gt, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 > b2)
      case Primitive(Lteq, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 <= b2)
      case Primitive(Gteq, NatLiteral(b1)::NatLiteral(b2)::Nil()) => BoolLiteral(b1 >= b2)
      case Primitive(Plus, NatLiteral(b1)::NatLiteral(b2)::Nil()) => NatLiteral(b1 + b2)
      case Primitive(Minus, NatLiteral(b1)::NatLiteral(b2)::Nil()) => NatLiteral(b1 - b2)
      case Primitive(Mul, NatLiteral(b1)::NatLiteral(b2)::Nil()) => NatLiteral(b1 * b2)
      case Primitive(Div, NatLiteral(b1)::NatLiteral(b2)::Nil()) if b2 != 0 => NatLiteral(b1 / b2)

      case Primitive(p, x::Nil())    if !isValue(x) => Primitive(p, smallStep(x)::Nil())
      case Primitive(p, x::y::Nil()) if !isValue(x) => Primitive(p, smallStep(x)::y::Nil())
      case Primitive(p, x::y::Nil()) if !isValue(y) => Primitive(p, x::smallStep(y)::Nil())
      case Primitive(_, _) => BottomTree /* Bad primitive or bad arguments */

      case _ => e
    }
  }

  def evaluate(e: Tree, fuel: BigInt): Tree = {
    require(fuel >= 0)
    decreases(fuel)
    if(isValue(e)) e
    else if(fuel == 0) BottomTree
    else evaluate(smallStep(e), fuel - 1)
  }
}