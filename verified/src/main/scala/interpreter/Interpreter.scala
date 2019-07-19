package interpreter

import trees._


import stainless.annotation._
import stainless.collection._
import stainless.lang._


object Interpreter {

  def isError(e: Tree): Boolean = {
    decreases(e)
    e match {
      case ErrorTree(_, _) => true
      case _ => false
    }
  }

  def isValue(e: Tree): Boolean = {
    decreases(e)
    e match {
      case UnitLiteral => true
      case NatLiteral(_) => true
      case BoolLiteral(_) => true
      case Var(_) => true
      case Lambda(_, _) => true
      case Pair(t1, t2) => isValue(t1) && isValue(t2)
      case RightTree(t) => isValue(t)
      case LeftTree(t) => isValue(t)
      case _ => false
    }
  }

  def isBind(t: Tree): Boolean = t.isInstanceOf[Bind]

  def replaceBind(bind: Tree, v: Tree): Tree = {
    require(isBind(bind))
    bind match {
      case Bind(id, body) => replace(id, v, body)
      case t => t
    }

  }

  def replace(xvar: Identifier, v: Tree, body: Tree): Tree = {
    body match {
      case Var(yvar) if yvar == xvar => v
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
      case Bind(yvar, e) if (xvar == yvar) => body
      case Bind(yvar, e) => Bind(yvar, replace(xvar, v, e))
      case Lambda(tp, bind) => Lambda(tp, replace(xvar, v, bind))
      case Fix(tp, bind) => Fix(tp, replace(xvar, v, bind))
      case LetIn(tp, v1, bind) => LetIn(tp, replace(xvar, v, v1), replace(xvar, v, bind))
      case Match(t, t0, bind) => Match(replace(xvar, v, t), replace(xvar, v, t0), replace(xvar, v, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replace(xvar, v, t), replace(xvar, v, bind1), replace(xvar, v, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replace(xvar, v, _)))
      case _ => body
    }
  }

  def smallStep(e: Tree): Tree = {
    e match {
      case IfThenElse(BoolLiteral(true), t1, t2) => t1
      case IfThenElse(BoolLiteral(false), t1, t2) => t2
      case IfThenElse(ErrorTree(s, t), _, _) => ErrorTree(s, t)
      case IfThenElse(t, _, _) if isValue(t) => ErrorTree("Waiting bool in if", Some(BoolType))
      case IfThenElse(t, tt, tf) => IfThenElse(smallStep(t), tt, tf)

      case Pair(ErrorTree(s, t), _) => ErrorTree(s, t)
      case Pair(_, ErrorTree(s, t)) => ErrorTree(s, t)
      case Pair(t1, t2) if isValue(t1) => Pair(t1, smallStep(t2))
      case Pair(t1, t2) => Pair(smallStep(t1), t2)

      case First(ErrorTree(s, t)) => ErrorTree(s, t)
      case First(Pair(t1, t2)) => t1
      case First(t) if isValue(t) => ErrorTree("First wait a Pair", None())
      case First(t) => First(smallStep(t))

      case Second(ErrorTree(s, t)) => ErrorTree(s, t)
      case Second(Pair(t1, t2)) => t2
      case Second(t) if isValue(t) => ErrorTree("Second wait a Pair", None())
      case Second(t) => Second(smallStep(t))

      case App(ErrorTree(s, t), _) => ErrorTree(s, t)
      case App(_, ErrorTree(s, t)) => ErrorTree(s, t)
      case App(Lambda(_, bind), v) if isValue(v) && isBind(bind) => replaceBind(bind, v)
      case App(Lambda(tp, bind: Bind), t) => App(Lambda(tp, bind), smallStep(t))
      case App(f, _) if isValue(f) => ErrorTree("App wait a lambda abstraction", None()) // f is a value and not a lambda
      case App(f, v) => App(smallStep(f), v)
      case Fix(_, Bind(id, bind)) if isBind(bind) => replaceBind(bind, Lambda(None(), Bind(Identifier(0, "_"), e)))

      case Match(ErrorTree(s, t), _, _) => ErrorTree(s, t)
      case Match(NatLiteral(BigInt(0)), t0, _) => t0
      case Match(NatLiteral(n), _, bind) if isBind(bind) => replaceBind(bind, NatLiteral(n - 1))
      case Match(t, _, _) if isValue(t) => ErrorTree("Match wait a nat", Some(NatType))
      case Match(t, t0, bind) => Match(smallStep(t), t0, bind)
      //case Match(t, t0, notBind) => ErrorTree("Match wait a bind", None())

      case EitherMatch(ErrorTree(s, t), _, _) => ErrorTree(s, t)
      case EitherMatch(LeftTree(v), bind, _) if isBind(bind) => replaceBind(bind, v)
      case EitherMatch(RightTree(v), _, bind) if isBind(bind) => replaceBind(bind, v)
      case EitherMatch(t, _, _) if isValue(t) => ErrorTree("EitherMatch Wait a Left or a Right", None())
      case EitherMatch(t, b1, b2) => EitherMatch(smallStep(t), b1, b2)

      case LetIn(tp, ErrorTree(s, t), bind) => ErrorTree(s, t)
      case LetIn(tp, v, bind) if isValue(v) && isBind(bind) => replaceBind(bind, v)
      case LetIn(tp, t, bind) if isValue(t) => ErrorTree("LetIn should have a bind", None())
      case LetIn(tp, t, bind) => LetIn(tp, smallStep(t), bind)

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
      case Primitive(_, _) => ErrorTree("Bad Primitive operations", None())

      case LeftTree(e) => LeftTree(smallStep(e))
      case RightTree(e) => RightTree(smallStep(e))

      case _ => e
    }
  }

  def evaluate(e: Tree, fuel: BigInt): Tree = {
    require(fuel >= 0)
    decreases(fuel)
    if(isValue(e) || isError(e)) e
    else if(fuel == 0) ErrorTree("No more fuel", Some(BottomType))
    else evaluate(smallStep(e), fuel - 1)
  }
}
