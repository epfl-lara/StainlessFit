import trees._
import interpreter._
import printer._
import typechecker._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

object Main {

  val assertFun = """def assert(b: Bool): Unit = { if(b) () else val x = Error("Assertion failed") in () }"""

  def evalFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        val (t, _, max) = Tree.setId(value, stainless.lang.Map(), 0)
        Interpreter.evaluate(t, 1000) match {
          case ErrorTree(error, _) => throw new Exception(s"Error during evaluation.\n${error}")
          case v => v
        }
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

  def typeCheckFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        val (t, _, max) = Tree.setId(value, stainless.lang.Map(), 0)
        TypeChecker.infer(t, max) match {
          case ErrorResult => throw new Exception("Cannot typecheck file.\n")
          case InferResult(ty) =>
            ty
        }
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

  def evalFile(s: String): Tree = evalFile(new File(s))

  def typeCheckFile(s: String): Tree = typeCheckFile(new File(s))

  def printHelp() = {
    println(
      """|Usage: run eval FILE
      |
      """.stripMargin)
  }

  def main(args: Array[String]): Unit = {
    if (args.length == 0) printHelp()
    else {
      args(0) match {
        case "eval" if (args.length == 2) =>
          println(evalFile(args(1)))
        case "typecheck" if (args.length == 2) =>
          val t = typeCheckFile(args(1))
          println("=======")
          println(Printer.pprint(t))
        case _ =>
          printHelp()
      }
    }
  }
}
