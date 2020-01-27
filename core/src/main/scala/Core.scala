package core

import core.trees._
import core.interpreter._
import core.typechecker._
import core.typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import core.Bench.bench

object Core {

  def parseString(s: String): Either[String, Tree] = {
    val it = s.iterator
    ScalaParser(ScalaLexer(it)) match {
      case ScalaParser.Parsed(value, _) =>
        Right(value)
      case ScalaParser.UnexpectedEnd(_) =>
        Left("Error during parsing: unexpected end.")
      case ScalaParser.UnexpectedToken(t, rest) =>
        Left(
          "Error during parsing: unexpected token:" + t + "\n" +
          "Expected instead one of:" + rest.first.mkString("   ")
        )
    }
  }

  def parseFile(f: File): Either[String, Tree] = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val regex = """Include\("(.*)"\)""".r
    val completeString = regex.replaceAllIn(s, m =>
      scala.io.Source.fromFile(new File(f.getAbsoluteFile().getParentFile().getCanonicalPath(), m.group(1))).getLines.mkString("\n") + "\n"
    )
    bench.time("Scallion parsing") { parseString(completeString) }
  }

  def evalFile(f: File): Either[String, Tree] =
    parseFile(f) flatMap { src =>
      val (t, _) = Tree.setId(src, Map(), 0)

      Interpreter.evaluate(t.erase()) match {
        case Error(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def typeCheckFile(f: File): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(f) flatMap { src =>
      val (t, max) = Tree.setId(src, Map(), 0)

      TypeChecker.infer(t, max) match {
        case None => Left(s"Could not type check: $f")
        case Some((success, tree)) =>
          bench.time("makeHTMLFile") {
            Derivation.makeHTMLFile(
              f,
              List(tree),
              success
            )
          }

          Right((success, tree))
      }
    }
  }

  def evalFile(s: String): Either[String, Tree] =
    evalFile(new File(s))

  def typeCheckFile(s: String): Either[String, (Boolean, NodeTree[Judgment])] =
    typeCheckFile(new File(s))

}
