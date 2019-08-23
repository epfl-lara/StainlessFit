package interpreter

import trees._


import stainless.annotation._
import stainless.collection._
import stainless.lang._


object Interpreter {
  var i = 0

  def smallStep(e: Tree): Tree = {
    e match {
      case IfThenElse(BooleanLiteral(true), t1, t2) => t1
      case IfThenElse(BooleanLiteral(false), t1, t2) => t2
      case IfThenElse(Error(s, t), _, _) => Error(s, t)
      case IfThenElse(t, _, _) if t.isValue => Error("Waiting bool in if", Some(BoolType))
      case IfThenElse(t, tt, tf) => IfThenElse(smallStep(t), tt, tf)

      case Pair(Error(s, t), _) => Error(s, t)
      case Pair(_, Error(s, t)) => Error(s, t)
      case Pair(t1, t2) if t1.isValue => Pair(t1, smallStep(t2))
      case Pair(t1, t2) => Pair(smallStep(t1), t2)

      case First(Error(s, t)) => Error(s, t)
      case First(Pair(t1, t2)) => t1
      case First(t) if t.isValue => Error("First wait a Pair", None())
      case First(t) => First(smallStep(t))

      case Second(Error(s, t)) => Error(s, t)
      case Second(Pair(t1, t2)) => t2
      case Second(t) if t.isValue => Error("Second wait a Pair", None())
      case Second(t) => Second(smallStep(t))

      case App(Error(s, t), _) => Error(s, t)
      case App(_, Error(s, t)) => Error(s, t)
      case App(Lambda(_, bind), v) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case App(Lambda(tp, bind: Bind), t) => App(Lambda(tp, bind), smallStep(t))
      case App(f, _) if f.isValue => Error("App wait a lambda abstraction", None()) // f is a value and not a lambda
      case App(f, v) => App(smallStep(f), v)
      case Fix(_, Bind(id, bind)) if bind.isBind => Tree.replaceBind(bind, Lambda(None(), Bind(Identifier(0, "_"), e)))

      case Match(Error(s, t), _, _) => Error(s, t)
      case Match(NatLiteral(BigInt(0)), t0, _) => t0
      case Match(NatLiteral(n), _, bind) if bind.isBind => Tree.replaceBind(bind, NatLiteral(n - 1))
      case Match(t, _, _) if t.isValue => Error("Match wait a nat", Some(NatType))
      case Match(t, t0, bind) => Match(smallStep(t), t0, bind)
      //case Match(t, t0, notBind) => Error("Match wait a bind", None())

      case EitherMatch(Error(s, t), _, _) => Error(s, t)
      case EitherMatch(LeftTree(v), bind, _) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case EitherMatch(RightTree(v), _, bind) if v.isValue && bind.isBind => Tree.replaceBind(bind, v)
      case EitherMatch(t, _, _) if t.isValue => Error("EitherMatch Wait a Left or a Right with binds.", None())
      case EitherMatch(t, b1, b2) => EitherMatch(smallStep(t), b1, b2)

      case Primitive(Not, Cons(BooleanLiteral(b), Nil())) => BooleanLiteral(!b)
      case Primitive(And, Cons(BooleanLiteral(b1), Cons(BooleanLiteral(b2), Nil()))) => BooleanLiteral(b1 && b2)
      case Primitive(Or, Cons(BooleanLiteral(b1), Cons(BooleanLiteral(b2), Nil()))) => BooleanLiteral(b1 || b2)

      case Primitive(Neq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 != n2)
      case Primitive(Eq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 == n2)
      case Primitive(Lt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 < n2)
      case Primitive(Gt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 > n2)
      case Primitive(Lteq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 <= n2)
      case Primitive(Gteq, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => BooleanLiteral(n1 >= n2)

      case Primitive(Plus, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => NatLiteral(n1 + n2)
      case Primitive(Minus, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) if n1 >= n2 => NatLiteral(n1 - n2)
      case Primitive(Mul, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) => NatLiteral(n1 * n2)
      case Primitive(Div, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))) if n2 != 0 => NatLiteral(n1 / n2)

      case Primitive(p, Cons(x, Nil())) if !x.isValue => Primitive(p, Cons(smallStep(x), Nil()))
      case Primitive(p, Cons(x, Cons(y, Nil()))) if !x.isValue => Primitive(p, Cons(smallStep(x), Cons(y, Nil())))
      case Primitive(p, Cons(x, Cons(y, Nil()))) if !y.isValue => Primitive(p, Cons(x, Cons(smallStep(y), Nil())))
      case Primitive(_, _) => Error(s"Bad Primitive operations $e", None())

      case LeftTree(e) => LeftTree(smallStep(e))
      case RightTree(e) => RightTree(smallStep(e))

      case _ => Error(s"Evaluation is stuck on (${e.getClass}) $e", Some(e))
    }
  }

  def evaluate(e: Tree, fuel: BigInt): Tree = {
    require(fuel >= 0)
    decreases(fuel)
    if(e.isValue || e.isError) e
    else if(fuel == 0) Error("No more fuel", Some(BottomType))
    else evaluate(smallStep(e), fuel - 1)
  }
}
