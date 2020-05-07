package stainlessfit
package core
package partialEvaluator

import trees._
import util.RunContext
import TreeUtils.replaceSmallStep
import parser.FitParser
import stainlessfit.core.util.Utils

object PartialEvaluator {
  val zero = BigInt(0)
  def subError(a: BigInt,b: BigInt) = s"Substraction between ${a} and ${b} will yield a negative value"
  def divError = s"Attempt to divide by zero"

  val __ignoreRefCounting__ = true

  //see erasure

  def smallStep(e: Tree)(implicit rc: RunContext, vars: Map[Identifier,Tree]): Option[Tree] = {
    def transform(e: Tree): Option[Tree] = {
      e match {
        case Var(id) => vars.get(id)
        case IfThenElse(BooleanLiteral(true), t1, _) =>  
          Some(t1)
        case IfThenElse(BooleanLiteral(false), _, t2) => 
          Some(t2)
        
        case First(Pair(t1,t2)) => 
          Some(t1)
        case Second(Pair(t1,t2)) => 
          Some(t2)

        case EitherMatch(LeftTree(lt), bl: Bind, _) => 
          Some(App(Lambda(None, bl), lt))
          //Some(Tree.replaceBind(bl, lt))
        case EitherMatch(RightTree(rt), _, br: Bind) =>
          Some(App(Lambda(None, br), rt))
          //Some(Tree.replaceBind(br, rt))
        
        case App(Lambda(_, bind: Bind), t2) if __ignoreRefCounting__ => 
          def rec(op: Option[Tree], old: Tree): (Option[Tree], Tree) = {
            op match{
              case Some(value) => 
                rec(TreeUtils.replaceBindSmallStep(bind, value), value)
              case None => (None, old)
            }
          }
          Some(Tree.replaceBind(bind, t2))

        case App(Lambda(_, bind: Bind), t2) =>
          //Counts the number of references to that variable; 0, 1 or 2+ (at least 2)
          TreeUtils.replaceBindSmallStep(bind, t2)
            .map(nT2 => TreeUtils.replaceBindSmallStep(bind, nT2).toRight(nT2)) match {
        /*0 */case None =>            Some(t2)
        /*1 */case Some(Right(t)) =>  Some(t)
        /*2+*/case Some(Left(t)) =>   None
          }

        case ErasableApp(t1, t2) => 
          Some(t1)//smallStep(t1)
        //case Size(t) => ???
        //case Lambda(None, bind) => ???
        //case Lambda(Some(tp), bind) => ???
        case ErasableLambda(tp, Bind(_,body)) => 
          Some(body)//smallStep(body)
        case Fix(_, bind) => 
          //TODO: avoid infinite loops
          //TODO: reference counting, or other means of avoiding code explosion
          Some(Tree.replaceBind(bind,e))
        //case LetIn(None, v1, bind) => ???
        //case LetIn(Some(tp), v1, bind) => ???
        //case MacroTypeDecl(tpe, bind) => ???
        //case MacroTypeInst(v1, args) => ???
        //case NatMatch(t, t0, bind) => ???

        case NatMatch(NatLiteral(`zero`), t0, _) => 
          Some(t0)
        case NatMatch(NatLiteral(n), _, bind: Bind) => 
          Some(App(Lambda(None,bind),NatLiteral(n-1)))

        case Primitive(Not, (BooleanLiteral(a) :: Nil)) =>                          Some(BooleanLiteral(!a))

        case Primitive(Or, (BooleanLiteral(true) :: _ :: Nil)) =>                   Some(BooleanLiteral(true))
        case Primitive(Or, (BooleanLiteral(a) :: BooleanLiteral(b) :: Nil)) =>      Some(BooleanLiteral(a || b))

        case Primitive(And, (BooleanLiteral(false) :: _ :: Nil)) =>                 Some(BooleanLiteral(false))
        case Primitive(And, (BooleanLiteral(a) :: BooleanLiteral(b) :: Nil)) =>     Some(BooleanLiteral(a && b))

        case Primitive(Plus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>            Some(NatLiteral(a + b))
        case Primitive(Minus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) => if(a>=b)  Some(NatLiteral(a - b))
                                                                          else      Some(Error(subError(a,b),None))
        case Primitive(Mul, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(NatLiteral(a * b))
        case Primitive(Div, (     _   :: NatLiteral(`zero`) :: Nil)) =>             Some(Error(divError, None))
        case Primitive(Div, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(NatLiteral(a / b))
        case Primitive(Eq,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a == b))
        case Primitive(Neq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a != b))
        case Primitive(Leq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a <= b))
        case Primitive(Geq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a >= b))
        case Primitive(Lt,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a < b))
        case Primitive(Gt,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(BooleanLiteral(a > b))

        //case Fold(tp, t) => ???
        //case Unfold(t, bind) => ???
        //case UnfoldPositive(t, bind) => ???
        //case Abs(Bind(_,body)) => smallStep(body)
        //case TypeApp(abs, t) => smallStep(abs)
        //case Error(_, _) => ???
        
        case _ => None
      }
    }
    replaceSmallStep(transform,e)
  }

  def evaluate(e: Tree)(implicit rc: RunContext): Tree = {
    println("=============================================")
    Printer.exprInfo(e)
    smallStep(e)(rc,Map()) match {
      case None => e
      case Some(value) => evaluate(value)
    }
  }
}