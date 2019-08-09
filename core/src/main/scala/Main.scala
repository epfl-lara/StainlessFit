import trees._
import interpreter._
import typechecker._
import typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object Main {

  val assertFun = """def assert(b: {b: Bool, b}): Unit = { if(b) () else Error[Unit]("Assertion failed") }"""

  def parseFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        value
      case ScalaParser.UnexpectedEnd(_) =>
        throw new java.lang.Exception("Error during parsing: unexpected end.\n")
      case ScalaParser.UnexpectedToken(t, _) =>
        throw new java.lang.Exception("Error during parsing: unexpected token." + t)
    }
  }

  def evalFile(f: File): Tree = {
    val src = parseFile(f)
    val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)
    Interpreter.evaluate(t, 100000) match {
      case ErrorTree(error, _) => throw new java.lang.Exception(s"Error during evaluation.\n${error}")
      case v => v
    }
  }

  def typeCheckFile(f: File): (Boolean, NodeTree[Judgment]) = {
    val src = parseFile(f)
    val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)
    TypeChecker.infer(t, max) match {
      case None() => throw new java.lang.Exception(s"Could not type check: $f")
      case Some((success, tree)) =>
        if (success)
          println(s"Type checked file $f successfully.")
        else
          println(s"Error while type checking file $f.")

        Derivation.makeHTMLFile(
          f,
          List(tree),
          success
        )

        (success, tree)
    }
  }

  def evalFile(s: String): Tree = evalFile(new File(s))

  def typeCheckFile(s: String): (Boolean, NodeTree[Judgment]) = typeCheckFile(new File(s))

  def printHelp() = {
    println(
      """|Usage: run eval FILE
         |       run typecheck FILE
         |       run typecheckWatch FILE
      """.stripMargin)
  }

  def main(args: Array[String]): Unit = {
    if (args.length == 0) printHelp()
    else {
      args(0) match {
        case "eval" if (args.length == 2) =>
          println(evalFile(args(1)))
        case "typecheck" if (args.length == 2) =>
          typeCheckFile(args(1))
        case "typecheckWatch" if (args.length == 2) =>
          new util.FileWatcher(
            scala.collection.immutable.Set((new java.io.File(args(1))).getAbsoluteFile),
            () =>
              try {
                typeCheckFile(args(1))
              } catch {
                case e: Throwable =>
                  println("ERROR: An exception was thrown")
                  e.printStackTrace()
              }
          ).run()
        case _ =>
          printHelp()
      }
    }
  }
}
