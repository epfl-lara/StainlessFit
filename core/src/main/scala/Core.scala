import verified.trees._
import verified.interpreter._
import verified.typechecker._
import verified.typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object Core {

  def parseString(s: String): Either[String, Tree] = {
    val it = s.iterator
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
    val regex = """Include\("(.*)"\)""".r
    val completeString = regex.replaceAllIn(s, m =>
      scala.io.Source.fromFile(new File(f.getAbsoluteFile().getParentFile().getCanonicalPath(), m.group(1))).getLines.mkString("\n") + "\n"
    )
    val res = parseString(completeString)
    // println("Parsed string")
    // println(res)
    // println("\n\n\n")
    res
  }

  def evalFile(f: File): Either[String, Tree] =
    parseFile(f) flatMap { src =>
      val (t, _) = Tree.setId(src, stainless.lang.Map(), 0)

      // println("Evaluating:")
      // println(t)
      // println("\nTerm after erasure:")
      // println(t.erase())

      Interpreter.evaluate(t.erase(), 1000000000) match {
        case Error(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def typeCheckFile(f: File): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(f) flatMap { src =>
      val (t, max) = Tree.setId(src, stainless.lang.Map(), 0)

      // println("Type-checking:")
      // println(t)

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
