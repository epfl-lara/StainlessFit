import trees._
import interpreter._
import printer._
import typechecker._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

object Main {

  val assertFun = """def assert(b: Bool): Unit = { if(b) () else val x = Error("Assertion failed") in () }"""

  def evalFile(f: File): (Result, Tree) = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        val ty = TypeChecker.infer(value)
        Interpreter.evaluate(value, 1000000000) match {
          case ErrorTree(error, _) => throw new Exception(s"Error during evaluation.\n${error}")
          case v => (ty, v)
        }
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

  def typeCheckFile(f: File): Result = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        TypeChecker.infer(value)
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

  def evalFile(s: String): (Result, Tree) = evalFile(new File(s))

  def typeCheckFile(s: String): Result = typeCheckFile(new File(s))

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
          val (ty, v) = evalFile(args(1))
          println(ty)
          println(Printer.pprint(v))
        case "typecheck" if (args.length == 2) =>
          println(typeCheckFile(args(1)))
        case _ =>
          printHelp()
      }
    }
  }
}
