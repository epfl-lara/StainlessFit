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
  def subError(a: BigInt,b: BigInt) = Error(s"Subtraction between ${a} and ${b} will yield a negative value", None)
  def divError = Error(s"Attempt to divide by zero", None)

  val __ignoreRefCounting__ = false

  //see erasure

  def smallStep(e: Tree, previousMeasure: Option[BigInt] = None)(implicit rc: RunContext): Option[(Tree, Option[BigInt])] = {
    def replaceNoFix(e: Tree): Option[Tree] = {
      e match {
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
        
        case App(Lambda(_, bind@Bind(id, body)), varValue) => 
          //TODO When implementing leaf-ness, be careful with Errors as they contain expressions
          /*
          def rec(t: Tree, replaceCount: BigInt): Option[Tree] = {
            TreeUtils.replaceVarSmallStep(id, t, varValue) match{
              case Some(newT) => 
                if(__ignoreRefCounting__ || replaceCount < 1){
                  rec(newT, replaceCount+1)
                }else {
                  None
                }
              case None => 
                Some(t)
            }
          }*/
          //Some(Tree.replaceBind(bind, varValue))
          //rec(body, 0)
          def simpleValue(v: Tree): Boolean = v match {
            case Var(_) => true
            case BooleanLiteral(b) => true
            case NatLiteral(n) => true
            case UnitLiteral => true
            case Error(s, opT) => opT.forall(simpleValue(_)) //returns true if None
            case _ => false 
          }

          lazy val (t, count) = Tree.replaceAndCount(id, varValue, body)

          if(__ignoreRefCounting__ || simpleValue(varValue)){
            Some(Tree.replaceBind(bind, varValue))
          }else if(count <= 1){
            Some(t)
          }else{
            None
          }
        /*
        case App(Lambda(_, bind@Bind(_, bindBody)), t2) =>
          //Counts the number of references to that variable; 0, 1 or 2+ (at least 2)
          TreeUtils.replaceBindSmallStep(bind, t2)
            .map(nT2 => TreeUtils.replaceBindSmallStep(bind, nT2).toRight(nT2)) match {
        /*0 */case None =>            Some(bindBody) //Should it be t2 ?
        /*1 */case Some(Right(t)) =>  Some(t)
        /*2+*/case Some(Left(t)) =>   None
          }
          */

        case ErasableApp(t1, t2) => 
          Some(t1)//smallStep(t1)
        //case Size(t) => ???
        //case Lambda(None, bind) => ???
        //case Lambda(Some(tp), bind) => ???
        case ErasableLambda(tp, Bind(_,body)) => 
          Some(body)//smallStep(body)
        /*
        case Fix(_, Bind(id, bind: Bind)) => 
          //TODO: avoid infinite loops
          //TODO: reference counting, or other means of avoiding code explosion
          //Some(Tree.replaceBind(bind,e))
          Some(App(Lambda(None, bind), e))
          //transform(App(Lambda(None, bind), e))
          */
        //case LetIn(None, v1, bind) => ???
        //case LetIn(Some(tp), v1, bind) => ???
        //case MacroTypeDecl(tpe, bind) => ???
        //case MacroTypeInst(v1, args) => ???
        //case NatMatch(t, t0, bind) => ???

        case NatMatch(NatLiteral(`zero`), t0, _) => 
          Some(t0)
        case NatMatch(NatLiteral(n), _, bind: Bind) => 
          Some(App(Lambda(None,bind),NatLiteral(n-1)))
        
        case Primitive(_, ((err: Error) :: _)) =>                                   Some(err)
        case Primitive(op, (_ :: (err: Error) :: Nil)) if !op.isBoolToBoolBinOp =>  Some(err)
        //Note that BoolToBoolBinOps have to be removed, because a certain value of the first argument could short circuit them out of the error

        case Primitive(Not, (BooleanLiteral(a) :: Nil)) =>                          Some(BooleanLiteral(!a))

        case Primitive(Or, (BooleanLiteral(true) :: _ :: Nil)) =>                   Some(BooleanLiteral(true))
        case Primitive(Or, (BooleanLiteral(false) :: t2 :: Nil)) =>                 Some(t2)
        case Primitive(Or, (t1 :: BooleanLiteral(false) :: Nil)) =>                  Some(t1)

        case Primitive(And, (BooleanLiteral(false) :: _ :: Nil)) =>                 Some(BooleanLiteral(false))
        case Primitive(And, (BooleanLiteral(true) :: t2 :: Nil)) =>                 Some(t2)
        case Primitive(And, (t1 :: BooleanLiteral(true) :: Nil)) =>                 Some(t1)

        case Primitive(Plus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>            Some(NatLiteral(a + b))
        case Primitive(Minus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) => if(a>=b)  Some(NatLiteral(a - b))
                                                                          else      Some(subError(a,b))
        case Primitive(Mul, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             Some(NatLiteral(a * b))
        case Primitive(Div, (     _   :: NatLiteral(`zero`) :: Nil)) =>             Some(divError)
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
    def replaceFix(e: Tree): Option[Tree] = {
      e match {
        case Fix(_, Bind(id, bind: Bind)) => 
          Some(App(Lambda(None, bind), e))
        case _ => None 
      }
    }
    replaceSmallStep(replaceNoFix,e).map( (_, None) ) orElse { 
      val op = replaceSmallStep(replaceFix,e)
      op match {
        case None => None
        case Some(tree) => 
          val measure = TreeSize(tree)
          val smaller = previousMeasure.map( _ > measure) getOrElse true
          Option.when(smaller)((tree, Some(measure)))
      }
    }
    //post condition: res.map( (_, op) => (previousMeasure != None) implies (op != None) ) getOrElse true
  }

  def evaluate(e: Tree, previousMeasure: Option[BigInt] = None)(implicit rc: RunContext): Tree = {
    
    //Printer.exprInfo(e)
    //println(s"=============================================${previousMeasure}")
    //Thread.sleep(1000)
    
    smallStep(e, previousMeasure) match {
      case None => e
      case Some((value, measure)) => 
        val postCond = previousMeasure match {
          case None => true
          case Some(prev) => 
            measure match {
              case None => true
              case Some(curr) => curr < prev
            }
        }
        if(!postCond){
          rc.reporter.fatalError(s"previousMeasure: $previousMeasure, measure: $measure")
        }
        val currentMeasure = measure orElse previousMeasure
        evaluate(value, currentMeasure)
    }
  }
}