package stainlessfit
package core
package partialEvaluator

import trees._
import util.RunContext
import parser.FitParser
import stainlessfit.core.util.Utils

object PartialEvaluator {
  val BigZero = BigInt(0)
  def subError(a: BigInt,b: BigInt) = s"Substraction between ${a} and ${b} will yield a negative value"
  def divError() = s"Attempt to divide by zero"

  //see erasure
  //see utils mapFirst

  def smallStep(e: Tree)(implicit rc: RunContext, vars: Map[Identifier,Tree]): Option[Tree] = {
    e match {
      case Var(id) => vars.get(id)
      case UnitLiteral => None
      case NatLiteral(_) => None
      case BooleanLiteral(_) => None
      case IfThenElse(cond, t1, t2) => 
        cond match{
          case BooleanLiteral(true) => Some(t1)
          case BooleanLiteral(false) => Some(t2)
          case _ => 
            smallStep(cond).map(IfThenElse(_,t1,t2)) orElse
            smallStep(t1).map(IfThenElse(cond,_,t2)) orElse
            smallStep(t2).map(IfThenElse(cond,t1,_))
        }
      case First(t) => 
        smallStep(t).map(First(_)) orElse (t match{
          case Pair(t1,t2) => Some(t1)
          case _ => None
        })
      case Second(t) => 
        smallStep(t).map(Second(_)) orElse (t match{
          case Pair(t1,t2) => Some(t2)
          case _ => None
        })
      case Pair(t1, t2) =>
        smallStep(t1).map(Pair(_,t2)) orElse
        smallStep(t2).map(Pair(t1,_))
      case EitherMatch(t, bind1, bind2) =>
        smallStep(t).map(EitherMatch(_,bind1,bind2)) orElse {
          t match {
            case LeftTree(lt) => ???
            case RightTree(rt) => ???
            case _ => ???
          }
        }
      case LeftTree(t) => smallStep(t).map(LeftTree(_))
      case RightTree(t) => smallStep(t).map(RightTree(_))
      case App(t1, t2) => ???
      case ErasableApp(t1, t2) => smallStep(t1)
      case Size(t) => ???
      case Lambda(None, bind) => ???
      case Lambda(Some(tp), bind) => ???
      case ErasableLambda(tp, Bind(_,body)) => smallStep(body)
      case Fix(None, bind) => ???
      case Fix(Some(tp), bind) => ???
      case LetIn(None, v1, bind) => ???
      case LetIn(Some(tp), v1, bind) => ???
      case MacroTypeDecl(tpe, bind) => ???
      case MacroTypeInst(v1, args) => ???
      case NatMatch(t, t0, bind) => ???
      case Primitive(op, arg1 :: rest) =>
        smallStep(arg1).map(x => Primitive(op, x :: rest)) orElse
        {(op, arg1, rest) match {
          case (Not, BooleanLiteral(a), Nil) =>           Some(BooleanLiteral(!a))
          case (And, BooleanLiteral(false), _ :: Nil) =>  Some(BooleanLiteral(false))
          case (Or, BooleanLiteral(true), _ :: Nil) =>    Some(BooleanLiteral(true))
          case _ =>                                       None
        }} orElse { rest.headOption.flatMap{ arg2 => //assumes there is never three arguments
          smallStep(arg2).map( x => Primitive(op, arg1 :: x :: Nil)) orElse 
          {(op,arg1,arg2) match {
            case (And, BooleanLiteral(a), BooleanLiteral(b)) =>     Some(BooleanLiteral(a && b))
            case (Or,  BooleanLiteral(a), BooleanLiteral(b)) =>     Some(BooleanLiteral(a || b))
            case (Plus, NatLiteral(a), NatLiteral(b)) =>            Some(NatLiteral(a + b))
            case (Minus, NatLiteral(a), NatLiteral(b)) => if(a>=b)  Some(NatLiteral(a - b))
                                                          else      Some(Error(subError(a,b),None))
            case (Mul, NatLiteral(a), NatLiteral(b)) =>             Some(NatLiteral(a * b))
            case (Div, NatLiteral(a), NatLiteral(b)) => if(b != 0)  Some(NatLiteral(a / b))
                                                        else        Some(Error(divError, None))
            case (Eq, NatLiteral(a), NatLiteral(b)) =>              Some(BooleanLiteral(a == b))
            case (Neq, NatLiteral(a), NatLiteral(b)) =>             Some(BooleanLiteral(a != b))
            case (Leq, NatLiteral(a), NatLiteral(b)) =>             Some(BooleanLiteral(a <= b))
            case (Geq, NatLiteral(a), NatLiteral(b)) =>             Some(BooleanLiteral(a >= b))
            case (Lt, NatLiteral(a), NatLiteral(b)) =>              Some(BooleanLiteral(a < b))
            case (Gt, NatLiteral(a), NatLiteral(b)) =>              Some(BooleanLiteral(a > b))
            case _ =>                                               None
          }}
        }}
      case Fold(tp, t) => ???
      case Unfold(t, bind) => ???
      case UnfoldPositive(t, bind) => ???
      case Abs(Bind(_,body)) => smallStep(body)
      case TypeApp(abs, t) => smallStep(abs)
      case Error(_, _) => ???
      

      case _ => throw new java.lang.Exception(s"Function `PartialEvaluator.smallStep` is not implemented on $e (${e.getClass}).")
    }
  }

  def evaluate(e: Tree)(implicit rc: RunContext): Tree = {
    Printer.exprInfo(e)
    smallStep(e)(rc,Map()) match {
      case None => e
      case Some(value) => evaluate(value)
    }
  }
  /*
  def partEval(e: Tree)(implicit rc: RunContext, vars: Map[Identifier,Tree]): Tree = {
    e match {
      case Var(id) => vars.getOrElse(id,e)
      case UnitLiteral => e
      case NatLiteral(_) => e
      case BooleanLiteral(_) => e
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
      case First(t) => 
        val eval = partEval(t)
        eval match{
          case Pair(t1,t2) => t1
          case _ => First(eval)
        }
      case Second(t) => 
        val eval = partEval(t)
        eval match{
          case Pair(t1,t2) => t2
          case _ => Second(eval)
        }
      case Pair(t1, t2) => Pair(partEval(t1),partEval(t2))
      case EitherMatch(t, bind1, bind2) =>
        val eval = partEval(t)
        eval match {
          case LeftTree(lt) => 
            ??? //eval can be anything => potential for code explosion
          case RightTree(rt) =>
            ??? //eval can be anything => potential for code explosion
          case _ => EitherMatch(eval,partEval(bind1),partEval(bind2))
        }
      case LeftTree(t) => LeftTree(partEval(t))
      case RightTree(t) => RightTree(partEval(t))
      case App(t1, t2) => ???
      case Size(t) => ???
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

      case BottomType => e
      case TopType => e
      

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $e (${e.getClass}).")
    }
  }
  */
}