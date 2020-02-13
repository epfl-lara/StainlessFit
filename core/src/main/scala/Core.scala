package stainlessfit
package core

import core.trees._
import core.interpreter._
import core.typechecker._
import core.typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import core.util.RunContext

object Core {

  def parseString(s: String): Either[String, Tree] = {
    val it = s.iterator
    ScalaParser(ScalaLexer(it)) match {
      case ScalaParser.LL1.Parsed(value, _) =>
        Right(value)
      case ScalaParser.LL1.UnexpectedEnd(rest) =>
        Left(
          s"""|Error during parsing, unexpected end of input.
              |Expected token: ${rest.first.mkString("   ")}""".stripMargin
        )
      case ScalaParser.LL1.UnexpectedToken(t, rest) =>
        Left(
          s"""|Error during parsing, unexpected token at position ${t.pos}: $t
              |Expected token: ${rest.first.mkString("   ")}""".stripMargin
        )
    }
  }

  def parseFile(rc: RunContext, f: File): Either[String, Tree] = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val regex = """Include\("(.*)"\)""".r
    val completeString = regex.replaceAllIn(s, m =>
      scala.io.Source.fromFile(new File(f.getAbsoluteFile().getParentFile().getCanonicalPath(), m.group(1))).getLines.mkString("\n") + "\n"
    )
    rc.bench.time("Scallion parsing") { parseString(completeString) }
  }

  val primitives = Map(
    Identifier(0, "size") -> Identifier(0, "size"),
    Identifier(0, "left") -> Identifier(0, "left"),
    Identifier(0, "right") -> Identifier(0, "right"),
    Identifier(0, "first") -> Identifier(0, "first"),
    Identifier(0, "second") -> Identifier(0, "second"),
  )

  def replacePrimitives(t: Tree): Tree = {
    t.replaceMany(subTree => subTree match {
      case App(Var(Identifier(0, "size")), e) => Some(Size(e))
      case App(Var(Identifier(0, "left")), e) => Some(LeftTree(e))
      case App(Var(Identifier(0, "right")), e) => Some(RightTree(e))
      case App(Var(Identifier(0, "first")), e) => Some(First(e))
      case App(Var(Identifier(0, "second")), e) => Some(Second(e))
      case _ => None
    })
  }

  def evalFile(f: File)(implicit rc: RunContext): Either[String, Tree] =
    parseFile(rc, f) flatMap { src =>
      val (t1, _) = Tree.setId(src, primitives, 0)
      val t2 = replacePrimitives(t1)

      Interpreter.evaluate(t2.erase()) match {
        case Error(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def typeCheckFile(f: File, html: Boolean)(implicit rc: RunContext): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(rc, f) flatMap { src =>
      val (t1, max) = Tree.setId(src, primitives, 0)
      val t2 = replacePrimitives(t1)

      new TypeChecker().infer(t2, max) match {
        case None => Left(s"Could not typecheck: $f")
        case Some((success, tree)) =>
          if (html)
            rc.bench.time("makeHTMLFile") {
              util.HTMLOutput.makeHTMLFile(rc, f, List(tree), success)
            }

          Right((success, tree))
      }
    }
  }

  def evalFile(s: String)(implicit rc: RunContext): Either[String, Tree] =
    evalFile(new File(s))

  def typeCheckFile(s: String, html: Boolean)(implicit rc: RunContext): Either[String, (Boolean, NodeTree[Judgment])] =
    typeCheckFile(new File(s), html)

}
