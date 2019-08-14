import trees._
import interpreter._
import typechecker._
import typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object Core {

  def parseString(s: String): Either[String, Tree] = {
    val it = s.toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        Right(value)
      case ScalaParser.UnexpectedEnd(_) =>
        Left("Error during parsing: unexpected end.")
      case ScalaParser.UnexpectedToken(t, _) =>
        Left("Error during parsing: unexpected token." + t)
    }
  }

  def parseFile(f: File): Either[String, Tree] = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val regex = """Include\("(.*)\.sc"\)""".r
    val completeString = regex.replaceAllIn(s, m => scala.io.Source.fromFile(new File(m.group(1) + ".sc")).getLines.mkString("\n"))
    parseString(completeString)
  }

  def evalFile(f: File): Either[String, Tree] =
    parseFile(f) flatMap { src =>
      val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)

      Interpreter.evaluate(t.erase(), 100000000) match {
        case ErrorTree(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def typeCheckFile(f: File): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(f) flatMap { src =>
      val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)
      TypeChecker.infer(t, max) match {
        case None() => Left(s"Could not type check: $f")
        case Some((success, tree)) =>
          Derivation.makeHTMLFile(
            f,
            List(tree),
            success
          )

          Right((success, tree))
      }
    }
  }

  def evalFile(s: String): Either[String, Tree] =
    evalFile(new File(s))

  def typeCheckFile(s: String): Either[String, (Boolean, NodeTree[Judgment])] =
    typeCheckFile(new File(s))

}
