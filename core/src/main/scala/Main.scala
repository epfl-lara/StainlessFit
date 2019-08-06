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

  def evalFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        val (t, _, max) = Tree.setId(value, stainless.lang.Map(), 0)
        Interpreter.evaluate(t, 100000) match {
          case ErrorTree(error, _) => throw new java.lang.Exception(s"Error during evaluation.\n${error}")
          case v => v
        }
      case t =>
        throw new java.lang.Exception("Error during parsing:\n" + t)
    }
  }

  def typeCheckFile(f: File): Unit = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        val (t, _, max) = Tree.setId(value, stainless.lang.Map(), 0)
        TypeChecker.infer(t, max) match {
          case None() => throw new java.lang.Exception(s"Could not type check: $f")
          case Some((success, trees)) =>
            if (success)
              println(s"Type checked file $f successfully.")
            else
              println(s"Error while type checking file $f.")

            Derivation.makeHTMLFile(
              f,
              List(trees),
              success
            )
        }
      case t =>
        throw new java.lang.Exception("Error during parsing:\n" + t)
    }
  }

  def evalFile(s: String): Tree = evalFile(new File(s))

  def typeCheckFile(s: String): Unit = typeCheckFile(new File(s))

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
