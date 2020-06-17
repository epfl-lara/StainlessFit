package stainlessfit
package core
package partialEvaluator

import java.io.File
import java.io.BufferedWriter
import java.io.FileWriter
import smtlib.printer.Printer
import trees._
import util.RunContext
import TreeUtils.replaceSmallStep
import parser.FitParser
import stainlessfit.core.util.Utils
import interpreter.Interpreter

object PartialEvaluator {
  val zero = BigInt(0)
  def subError(a: BigInt,b: BigInt) = Error(s"Subtraction between ${a} and ${b} will yield a negative value", None)
  def divError = Error(s"Attempt to divide by zero", None)

  val __ignoreRefCounting__ = true
  val __ignoreMeasure__ = true

  //see erasure

  def smallStep(e: Tree, previousMeasure: Option[BigInt] = None)(implicit rc: RunContext): Option[(Tree, Option[BigInt])] = {
    def replaceNoFix(e: Tree): Option[Tree] = {
      e match {
        case IfThenElse(BooleanLiteral(true), t1, _) => 
          println("If(true)")
          Some(t1)
        case IfThenElse(BooleanLiteral(false), _, t2) => 
          println("If(false)")
          Some(t2)
        
        case First(Pair(t1,t2)) => 
          println("First(pair)")
          Some(t1)
        case Second(Pair(t1,t2)) => 
          println("Second(pair)")
          Some(t2)

        case EitherMatch(LeftTree(lt), bl: Bind, _) => 
          println("EitherMatch(left)")
          Some(App(Lambda(None, bl), lt))
        case EitherMatch(RightTree(rt), _, br: Bind) => 
          println("EitherMatch(right)")
          Some(App(Lambda(None, br), rt))
        
        case App(Lambda(_, bind@Bind(id, body)), varValue) => 

          def simpleValue(v: Tree): Boolean = v match {
            case Var(_) => true
            case BooleanLiteral(b) => true
            case NatLiteral(n) => true
            case UnitLiteral => true
            case Error(s, opT) => opT.forall(simpleValue(_)) //returns true if None
            case _ => false 
          }

          lazy val (t, count) = Tree.replaceAndCount(id, varValue, body)
          if(__ignoreRefCounting__){
            println(s"App(lambda) no ref count: $id")//: $varValue")
            Some(Tree.replaceBind(bind, varValue))
          }else if(simpleValue(varValue)){
            println("App(lambda) simplevalue")
            Some(Tree.replaceBind(bind, varValue))
          }else if(count <= 1){
            println("App(lambda) ref <= 1")
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
          println("NatMatch(0)")
          Some(t0)
        case NatMatch(NatLiteral(n), _, bind: Bind) => 
          println("NatMatch(n)")
          Some(App(Lambda(None,bind),NatLiteral(n-1)))
        
        case Primitive(_, ((err: Error) :: _)) =>                                   Some(err)
        case Primitive(op, (_ :: (err: Error) :: Nil)) if !op.isBoolToBoolBinOp =>  Some(err)
        //Note that BoolToBoolBinOps have to be removed, because a certain value of the first argument could short circuit them out of the error

        case Primitive(Not, (BooleanLiteral(a) :: Nil)) =>                          Some(BooleanLiteral(!a))

        case Primitive(Or, (BooleanLiteral(true) :: _ :: Nil)) =>                   Some(BooleanLiteral(true))
        case Primitive(Or, (BooleanLiteral(false) :: t2 :: Nil)) =>                 Some(t2)
        case Primitive(Or, (t1 :: BooleanLiteral(false) :: Nil)) =>                 Some(t1)

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
          println("Fix")
          Some(App(Lambda(None, bind), e))
        case _ => None 
      }
    }
    replaceSmallStep(replaceNoFix,e).map( (_, None) ) orElse { 
      val op = replaceSmallStep(replaceFix,e)
      if(__ignoreMeasure__){
        op.map((_, None))
      }else{
        op match {
          case None => None
          case Some(tree) => 
            val measure = TreeSize(tree)
            val smaller = previousMeasure.map( _ > measure) getOrElse true
            Option.when(smaller)((tree, Some(measure)))
        }
      }
    }
    //post condition: res.map( (_, op) => (previousMeasure != None) implies (op != None) ) getOrElse true
  }

  def writeFile(filename: String, s: String): Unit = {
      val file = new File(filename)
      val bw = new BufferedWriter(new FileWriter(file))
      bw.write(s)
      bw.close()
  }

  def writeTreeToFile(filename: String, tree: Tree)(implicit rc: RunContext): Unit = {
    val folder = "error\\"
    val path = s"$folder$filename"
    writeFile(path, Printer.exprAsString(tree))
    println(s"wrote to $path")
  }

  def evaluate(e: Tree, previousMeasure: Option[BigInt] = None, pastEval: Option[Tree] = None)(implicit rc: RunContext): Tree = {
    
    //Printer.exprInfo(e)
    //println(s"=============================================${previousMeasure}")
    //Thread.sleep(1000)
    
    smallStep(e, previousMeasure) match {
      case None => e
      case Some((value, measure)) => 
        val postCond1 = previousMeasure match {
          case None => true
          case Some(prev) => 
            measure match {
              case None => true
              case Some(curr) => curr < prev
            }
        }
        if(!postCond1){
          rc.reporter.fatalError(s"First postcond fail: previousMeasure: $previousMeasure, measure: $measure")
        }

        lazy val afterEval = Interpreter.evaluate(value)
        val usePost2 = true
        lazy val postCond2 = pastEval.map(_ == afterEval) getOrElse true
      
        if(usePost2 && !postCond2){
          writeTreeToFile("oldTree.sf",e)
          writeTreeToFile("oldEval.sf",pastEval.get)
          writeTreeToFile("newTree.sf",value)
          writeTreeToFile("newEval.sf",afterEval)
          rc.reporter.fatalError(s"Second postcond fail: \nold tree: $e \npartevaled tree: \n${Printer.exprAsString(value)}\nevaluates to: \n${Printer.exprAsString(afterEval)}\nBut old evaluated tree was: \n${pastEval.map(Printer.exprAsString(_)).getOrElse("")}")
        }
        
        val currentMeasure = measure orElse previousMeasure
        evaluate(value, currentMeasure, Some(afterEval))
    }
  }
}