package interpreter

import _root_.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

object Interpreter {

  def isValue(e: Tree): Boolean = {
    decreases(e)
    e match {
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
  }

  def replaceBind(bind: Bind, v: Tree): Tree = {
    bind match {
      case Bind(None(), body) => body
      case Bind(Some(xvar), body) => replace(xvar, v, body)
    }
  }

  def replace(xvar: Var, v: Tree, body: Tree): Tree = {
    body match {
      case yvar: Var if yvar == xvar => v
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
      case Fix(tp, Bind(n, bind)) => replace(xvar, v, bind) match {
        case b: Bind => Fix(tp, Bind(n, b))
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

  def smallStep(e: Tree): Tree = {
    e match {
      case IfThenElse(BoolLiteral(true), t1, t2) => t1
      case IfThenElse(BoolLiteral(false), t1, t2) => t2
      case IfThenElse(t, _, _) if isValue(t) => BottomTree
      case IfThenElse(t, tt, tf) => IfThenElse(smallStep(t), tt, tf)

      case Pair(t1, t2) if isValue(t1) => Pair(t1, smallStep(t2))
      case Pair(t1, t2) => Pair(smallStep(t1), t2)

      case First(Pair(t1, t2)) => t1
      case First(t) if isValue(t) => BottomTree
      case First(t) => First(smallStep(t))

      case Second(Pair(t1, t2)) => t2
      case Second(t) if isValue(t) => BottomTree
      case Second(t) => Second(smallStep(t))

      case App(Lambda(_, bind: Bind), v) if isValue(v) => replaceBind(bind, v)
      case App(Lambda(tp, bind: Bind), t) => App(Lambda(tp, bind), smallStep(t))
      case App(f, _) if isValue(f) => BottomTree // f is a value and not a lambda
      case App(f, v) => App(smallStep(f), v)
      case Fix(_, Bind(_, bind: Bind)) => replaceBind(bind, Lambda(None(), Bind(None(), e)))

      case Match(NatLiteral(BigInt(0)), t0, _) => t0
      case Match(NatLiteral(n), _, bind: Bind) => replaceBind(bind, NatLiteral(n - 1))
      case Match(t, _, _) if isValue(t) => BottomTree
      case Match(t, t0, bind: Bind) => Match(smallStep(t), t0, bind)

      case EitherMatch(LeftTree(v), bind: Bind, _) => replaceBind(bind, v)
      case EitherMatch(RightTree(v), _, bind: Bind) => replaceBind(bind, v)
      case EitherMatch(t, _, _) if isValue(t) => BottomTree
      case EitherMatch(t, b1: Bind, b2: Bind) => EitherMatch(smallStep(t), b1, b2)

      case LetIn(tp, v, bind: Bind) => replaceBind(bind, v)

      case Primitive(Not, Cons(BoolLiteral(b), Nil())) => BoolLiteral(!b)
      case Primitive(And, Cons(BoolLiteral(b1), Cons(BoolLiteral(b2), Nil()))) => BoolLiteral(b1 && b2)
      case Primitive(Or, Cons(BoolLiteral(b1), Cons(BoolLiteral(b2), Nil()))) => BoolLiteral(b1 || b2)

      case Primitive(Neq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 != n2)
      case Primitive(Eq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 == n2)
      case Primitive(Lt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 < n2)
      case Primitive(Gt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 > n2)
      case Primitive(Lteq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 <= n2)
      case Primitive(Gteq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BoolLiteral(n1 >= n2)

      case Primitive(Plus, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => NatLiteral(n1 + n2)
      case Primitive(Minus, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => NatLiteral(n1 - n2)
      case Primitive(Mul, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => NatLiteral(n1 * n2)
      case Primitive(Div, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) if n2 != 0 => NatLiteral(n1 / n2)

      case Primitive(p, Cons(x, Nil())) if !isValue(x) => Primitive(p, Cons(smallStep(x), Nil()))
      case Primitive(p, Cons(x, Cons(y, Nil()))) if !isValue(x) => Primitive(p, Cons(smallStep(x), Cons(y, Nil())))
      case Primitive(p, Cons(x, Cons(y, Nil()))) if !isValue(y) => Primitive(p, Cons(x, Cons(smallStep(y), Nil())))
      case Primitive(_, _) => BottomTree

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
