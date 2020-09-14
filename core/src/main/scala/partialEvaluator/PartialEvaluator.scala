package stainlessfit
package core
package partialEvaluator

import stainlessfit.core.extraction._
import java.io.File
import java.io.BufferedWriter
import java.io.FileWriter
import smtlib.printer.Printer
import trees._
import util.RunContext
import TreeUtils._
import parser.FitParser
import stainlessfit.core.util.Utils
import interpreter.Interpreter
import scala.io.StdIn._

object PartialEvaluator {
  def pipeline()(implicit rc: RunContext) =
        DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
        DebugPhase(new Namer(), "Namer") andThen
        DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
        DebugPhase(new Erasure(), "Erasure")



  val zero = BigInt(0)
  def subError(a: BigInt,b: BigInt) = Error(s"Subtraction between ${a} and ${b} will yield a negative value", None)
  def divError = Error(s"Attempt to divide by zero", None)

  val __ignoreMeasure__ = true
  val __debugPrint__ = false

  def smallStep(e: Tree, previousMeasure: Option[BigInt] = None, disableReferenceCounting: Boolean = true)(implicit rc: RunContext): Option[(Tree, Option[BigInt])] = {
    def replaceNoFix(e: Tree): Option[Tree] = {
      e match {
        case IfThenElse(BooleanLiteral(true), t1, _) => 
          if (__debugPrint__) println("If(true)")
          Some(t1)
        case IfThenElse(BooleanLiteral(false), _, t2) => 
          if (__debugPrint__) println("If(false)")
          Some(t2)
        
        case First(Pair(t1,t2)) => 
          if (__debugPrint__) println("First(pair)")
          Some(t1)
        case Second(Pair(t1,t2)) => 
          if (__debugPrint__) println("Second(pair)")
          Some(t2)

        case EitherMatch(LeftTree(lt), bl: Bind, _) => 
          if (__debugPrint__) println("EitherMatch(left)")
          Some(App(Lambda(None, bl), lt))
        case EitherMatch(RightTree(rt), _, br: Bind) => 
          if (__debugPrint__) println("EitherMatch(right)")
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

          //val varValue = _varValue.freshenIdentifiers()

          lazy val (t, count) = Tree.replaceAndCount(id, varValue, body)
          if(disableReferenceCounting){
            if (__debugPrint__) println(s"App(lambda) no ref count: $id")//: $varValue")
            Some(Tree.replaceBind(bind, varValue))
          }else if(simpleValue(varValue)){
            if (__debugPrint__) println(s"App(lambda) simplevalue: $id")
            Some(Tree.replaceBind(bind, varValue))
          }else if(count <= 1){
            if (__debugPrint__) println(s"App(lambda) ref <= 1: $id")
            Some(t)
          }else{
            None
          }

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
          if (__debugPrint__) println("NatMatch(0)")
          Some(t0)
        case NatMatch(NatLiteral(n), _, bind: Bind) => 
          if (__debugPrint__) println("NatMatch(n)")
          Some(App(Lambda(None,bind),NatLiteral(n-1)))
        
        case Primitive(_, ((err: Error) :: _)) =>                                   if (__debugPrint__) println("err _"); Some(err)
        case Primitive(op, (_ :: (err: Error) :: Nil)) if !op.isBoolToBoolBinOp =>  if (__debugPrint__) println("_ err"); Some(err)
        //Note that BoolToBoolBinOps have to be removed, because a certain value of the first argument could short circuit them out of the error

        case Primitive(Not, (BooleanLiteral(a) :: Nil)) =>                          if (__debugPrint__) println("!a"); Some(BooleanLiteral(!a))

        case Primitive(Or, (BooleanLiteral(true) :: _ :: Nil)) =>                   if (__debugPrint__) println("true || _"); Some(BooleanLiteral(true))
        case Primitive(Or, (BooleanLiteral(false) :: t2 :: Nil)) =>                 if (__debugPrint__) println("false || _"); Some(t2)
        case Primitive(Or, (t1 :: BooleanLiteral(false) :: Nil)) =>                 if (__debugPrint__) println("_ || false"); Some(t1)

        case Primitive(And, (BooleanLiteral(false) :: _ :: Nil)) =>                 if (__debugPrint__) println("false && _"); Some(BooleanLiteral(false))
        case Primitive(And, (BooleanLiteral(true) :: t2 :: Nil)) =>                 if (__debugPrint__) println("true && _"); Some(t2)
        case Primitive(And, (t1 :: BooleanLiteral(true) :: Nil)) =>                 if (__debugPrint__) println("_ && true"); Some(t1)

        case Primitive(Plus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>            if (__debugPrint__) println("a + b"); Some(NatLiteral(a + b))
        case Primitive(Minus, (NatLiteral(a) :: NatLiteral(b) :: Nil)) => if(a>=b)  {if (__debugPrint__) println("a - b"); Some(NatLiteral(a - b))}
                                                                          else      {if (__debugPrint__) println("a - b < 0"); Some(subError(a,b))}
        case Primitive(Mul, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a * b"); Some(NatLiteral(a * b))
        case Primitive(Div, (     _   :: NatLiteral(`zero`) :: Nil)) =>             if (__debugPrint__) println("_ / 0"); Some(divError)
        case Primitive(Div, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a / b"); Some(NatLiteral(a / b))
        case Primitive(Eq,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a == b"); Some(BooleanLiteral(a == b))
        case Primitive(Neq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a != b"); Some(BooleanLiteral(a != b))
        case Primitive(Leq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a <= b"); Some(BooleanLiteral(a <= b))
        case Primitive(Geq, (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a >= b"); Some(BooleanLiteral(a >= b))
        case Primitive(Lt,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a < b"); Some(BooleanLiteral(a < b))
        case Primitive(Gt,  (NatLiteral(a) :: NatLiteral(b) :: Nil)) =>             if (__debugPrint__) println("a > b"); Some(BooleanLiteral(a > b))
        

        //case Fold(tp, t) => ???
        //case Unfold(t, bind) => ???
        //case UnfoldPositive(t, bind) => ???
        //case Abs(Bind(_,body)) => smallStep(body)
        //case TypeApp(abs, t) => smallStep(abs)
        //case Error(_, _) => ???
        
        case _ => None
      }
    }
    def replaceFix(e: Tree, superTree: Option[(Tree, Int)]): Option[Tree] = {
      e match {
        case Fix(_, Bind(id, bind: Bind)) => 
          Option.when(superTree.isEmpty){
            if (__debugPrint__) println(s"Fix: ${bind.id}")
            //App(Lambda(None, bind), e)
            Tree.replaceBind(bind, e)
          }
          
        case _ => None 
      }
    }
    def fixTreeFilter(e: Tree, index: Int): Boolean = {
      val inside = index != 0
      e match {
        case _: IfThenElse => inside
        case _: EitherMatch => inside 
        case _: NatMatch => inside

        case _ => false
      }
    }

    replaceSmallStep(replaceNoFix,e).map( (_, None) ) orElse { 
      val op = replaceFirstConditionalOnSuperTree(replaceFix, e, fixTreeFilter)
      //replaceSmallStep(replaceFix,e)
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

  def evaluate(e: Tree, previousMeasure: Option[BigInt] = None, pastEval: Option[Tree] = None, disableReferenceCounting: Boolean = true)(implicit rc: RunContext): Tree = {
    if(__debugPrint__){
      println(s"=============================================${previousMeasure}")
      Printer.exprInfo(e)
    }
    //println(e)
    //Thread.sleep(1000)
    
    smallStep(e, previousMeasure) match {
      case None => e
      case Some((value, measure)) => 
        //readLine()
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
        val usePost2 = false
        
        val afterEvalOpt = Option.when(usePost2){
          val afterEval = Interpreter.evaluate(value)
          val postCond2 = pastEval.map(_ == afterEval) getOrElse true
          if(!postCond2){
            /*writeTreeToFile("oldTree.sf",e)
            writeTreeToFile("oldEval.sf",pastEval.get)
            writeTreeToFile("newTree.sf",value)
            writeTreeToFile("newEval.sf",afterEval)*/
            rc.reporter.fatalError(s"Second postcond fail: \nold tree: $e \npartevaled tree: \n${Printer.exprAsString(value)}\nevaluates to: \n${Printer.exprAsString(afterEval)}\nBut old evaluated tree was: \n${pastEval.map(Printer.exprAsString(_)).getOrElse("")}")
          }
          afterEval
        }
        
        
        val currentMeasure = measure orElse previousMeasure
        evaluate(value, currentMeasure, afterEvalOpt, disableReferenceCounting)
    }
  }
}