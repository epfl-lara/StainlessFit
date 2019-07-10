import trees._
import interpreter._
import printer._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

object Main {

  def evalFile(f: File): Tree = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = s.toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        Interpreter.evaluate(value, 1000000000)
      case t =>
        throw new Exception("Error during parsing:\n" + t)
    }
  }

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
  }
}
