package interpretor

import _root_.trees._

//import scala.collection.immutable.HashMap // for environment */

final case class InvalidExpressionException(private val message: String = "") extends Exception(message)


object Interpretor {

  def replace(xvar: Var, v: Tree, body: Tree): Tree = {
    val Var(id, x): Var = xvar
    body match {
      case NatLiteral(n) => body
      case BoolLiteral(b) => body
      case Var(id1, y) if (x == y && id1 == id) => v
      case Var(id1, y) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(
          replace(xvar, v, cond),
          replace(xvar, v, t1),
          replace(xvar, v, t2)
        )
      case App(t1, t2) =>
        App(replace(xvar, v, t1), replace(xvar, v, t2))
      case Tuple(s) => Tuple(s.map(replace(xvar, v, _)))
      case TupleSelect(t, i) => TupleSelect(replace(xvar, v, t), i)
      case Lambda(tp, Bind(Var(id1, y), body1)) if (x == y && id1 == id) =>
        body
      case Lambda(tp, Bind(Var(id1, y), body1)) =>
        Lambda(tp, Bind(Var(id1, y), replace(xvar, v, body1)))
      case Fix(Bind(Var(id1, y), body1)) if (x == y && id1 == id) => body
      case Fix(Bind(Var(id1, y), body1)) =>
        Fix(Bind(Var(id1, y), replace(xvar, v, body1)))
      case Bind(Var(id1, y), body1) if (x == y && id1 == id) =>
        body
      case Bind(y, body1) => Bind(y, replace(xvar, v, body1))
      case Match(t, t0, Bind(Var(id2, x2), t2)) =>
       val t2_ = if(id2 == id && x2 == x) t2 else (replace(xvar, v, t2))
        Match(
          replace(xvar, v, t),
          replace(xvar, v, t0),
          Bind(Var(id2, x2), t2_)
        )
      case EitherMatch(t, Bind(Var(id1, x1), t1), Bind(Var(id2, x2), t2)) =>
        val t1_ = if(id1 == id && x1 == x) t1 else (replace(xvar, v, t1))
        val t2_ = if(id2 == id && x2 == x) t2 else (replace(xvar, v, t2))
        EitherMatch(
          replace(xvar, v, t),
          Bind(Var(id1, x1), t1_),
          Bind(Var(id2, x2), t2_)
        )
      case Left(t) => Left(replace(xvar, v, t))
      case Right(t) => Right(replace(xvar, v, t))
      case Because(t1, t2) =>
        Because(replace(xvar, v, t1), replace(xvar, v, t2))
      case S(n) => S(replace(xvar, v, n))
      case P(n) => P(replace(xvar, v, n))
      case NatEq(t1, t2) =>
        NatEq(replace(xvar, v, t1), replace(xvar, v, t2))
    }
  }

  def evaluate(
    e: Tree,
    fuel: BigInt): (Tree, BigInt) = {
    if(fuel == BigInt(0))
      return (e, fuel)
    e match {
      case NatLiteral(n) => (e, fuel)
      case BoolLiteral(b) => (e, fuel)
      case Var(id, name) => (e, fuel)
      case IfThenElse(c, t1, t2) => {
        val (c1, fuel1): (Tree, BigInt) = evaluate(c, fuel)
        if(fuel1 == 0) return (e, 0)
        c1 match {
          case BoolLiteral(true)  => evaluate(t1, fuel1 - 1)
          case BoolLiteral(false) => evaluate(t2, fuel1 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case App(t1, t2) => {
        val (f, fuel1): (Tree, BigInt) = evaluate(t1, fuel)
        if(fuel1 == 0) return (e, 0)
        val (v, fuel2): (Tree, BigInt) = evaluate(t2, fuel1)
        if(fuel2 == 0) return (e, 0)
        f match {
          case Lambda(_, Bind(x, body)) =>
            evaluate(replace(x, v, body), fuel2 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case Tuple(s) => {
        val (s1, fuel1) = s.foldRight( (List(), fuel): (List[Tree], BigInt)) {
          case (t, (r, f))  =>
            val (t1, f1) = evaluate(t, f)
            (t1::r, f1)
        }
        (Tuple(s1), fuel1 - 1)
      }
      case TupleSelect(t, i) => { // Check if it is a tuple before => lazy evaluation
        val (v, fuel1): (Tree, BigInt) = evaluate(t, fuel)
        if(fuel1 == 0) return (e, 0)
        v match {
          case Tuple(s) => (s(i), fuel1 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case Fix(t) => {
        val (b, fuel1): (Tree, BigInt) = evaluate(t, fuel)
        if(fuel1 == 0) return (e, 0)
        b match {
          case Bind(x, body) =>
            val ret = replace(x, Fix(Bind(x, body)), body)
            evaluate(ret, fuel1 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case S(e1) => {
        val (x, fuel1): (Tree, BigInt) = evaluate(e1, fuel)
        if(fuel1 == 0) return (e, 0)
        x match {
          case NatLiteral(n) => (NatLiteral(n + 1), fuel1 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case P(e1) => {
        val (x, fuel1): (Tree, BigInt) = evaluate(e1, fuel)
        if(fuel1 == 0) return (e, 0)
        x match {
          case NatLiteral(n) => (NatLiteral(n - 1), fuel1 - 1)
          case _ => throw new InvalidExpressionException
        }
      }
      case NatEq(e1, e2) => {
        val (x, fuel1): (Tree, BigInt) = evaluate(e1, fuel)
        if(fuel1 == 0) return (e, 0)
        val (y, fuel2): (Tree, BigInt) = evaluate(e2, fuel1)
        if(fuel2 == 0) return (e, 0)
        (x, y) match {
          case (NatLiteral(n), NatLiteral(m)) => (BoolLiteral(n == m), fuel2 - 1)
          case (_, _) => throw new InvalidExpressionException
        }
      }
      case Match(t, t0, t1) => {
        val (en, fuel1): (Tree, BigInt) = evaluate(t, fuel)
        if(fuel1 == 0) return (e, 0)
        en match {
          case NatLiteral(n) => {
            if(n == 0) {
              evaluate(t0, fuel1 - 1)
            }
            else {
              val (b, fuel2): (Tree, BigInt) =  evaluate(t1, fuel1)
              b match {
                case Bind(x, body) => evaluate(replace(x, NatLiteral(n - 1), body), fuel2 - 1)
                case _ => throw new InvalidExpressionException
              }
            }
          }
          case _ => throw new InvalidExpressionException
        }
      }
      case EitherMatch(t1, t2, t3) => {
        val (e1, fuel1): (Tree, BigInt) = evaluate(t1, fuel)
        if(fuel1 == 0) {
          return (e, 0)
        }
        else {
          val ((e, fuel2), v): ((Tree, BigInt), Tree) =
            e1 match{
              case Left(v) => (evaluate(t2, fuel1), v)
              case Right(v) => (evaluate(t3, fuel1), v)
              case _ => throw new InvalidExpressionException
            }
            if(fuel2 == 0) return (e, 0)
          e match {
            case Bind(x, body) => evaluate(replace(x, v, body), fuel2 - 1)
            case _ => throw new InvalidExpressionException
          }
        }
      }
      case _ => (e, fuel)
    }
  }
}