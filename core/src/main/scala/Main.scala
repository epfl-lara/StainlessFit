import trees._
import interpreter._
import printer._
import typer._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

object Main {

  def evalFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val assertFun = """def assert(b: Bool): Unit = { if(b) () else Error("Assertion failed") }"""
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        Interpreter.evaluate(value, 1000000000) match {
          case ErrorTree(error, _) => throw new Exception(s"Error during evaluation.\n${error}")
          case v => v
        }
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

  /*def typeCheckFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
          TypeChecker.infer()
        }
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }*/

  def evalFile(s: String): Tree = evalFile(new File(s))

  def printHelp() = {
    println(
      """|Usage: run eval FILE
      """.stripMargin)
  }

  def main(args: Array[String]): Unit = {
    if (args.length == 0) printHelp()
    else {

      args(0) match {
        case "eval" if (args.length == 2) =>
          println(Printer.pprint(evalFile(args(1))))
        case _ =>
          printHelp()
      }
    }
    val e0 = Match(
      NatLiteral(0),
      NatLiteral(2),
      Bind(
        stainless.lang.Some(Identifier(stainless.lang.Some(0), "n")),
        Var(Identifier(stainless.lang.Some(0), "n"))
      )
    )
    val e1 = Lambda(
      stainless.lang.Some(NatType),
      Bind(
        stainless.lang.Some(Identifier(stainless.lang.Some(0), "n")),
        Primitive(Plus, stainless.collection.List(Var(Identifier(stainless.lang.Some(0), "n")), NatLiteral(2)))
      )
    )
    println(typer.TypeChecker.infer(e1))
  }
}
