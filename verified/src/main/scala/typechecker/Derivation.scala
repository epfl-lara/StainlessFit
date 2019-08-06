package typechecker

import java.io.FileWriter

import _root_.trees._
import _root_.interpreter._

import stainless.collection._
import stainless.lang._

object Derivation {

  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)

  sealed abstract class Judgment {
    val c: Context
  }

  def shortString(s: String, maxWidth: Int = 160): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  case class CheckJudgment(override val c: Context, e: Tree, t: Tree) extends Judgment {
    override def toString =
      s"⊢ ${termColor(shortString(e.toString))} ⇓ ${typeColor(shortString(t.toString))}"
  }

  case class InferJudgment(override val c: Context, e: Tree, t: Option[Tree]) extends Judgment {
    override def toString = t match {
      case None() => s"⊢ ${termColor(shortString(e.toString))} ⇑ ??"
      case Some(tpe) => s"⊢ ${termColor(shortString(e.toString))} ⇑ ${typeColor(shortString(tpe.toString))}"
    }
  }

  case class AreEqualJudgment(override val c: Context, t1: Tree, t2: Tree) extends Judgment {
    override def toString = s"⊢ ${typeColor(shortString(t1.toString))} =:= ${typeColor(shortString(t2.toString))}"
  }

  case class ErrorJudgment[T](override val c: Context, error: T) extends Judgment {
    override def toString = s"⊢ error: $error"
  }

  case class FileJudgment(override val c: Context, s: String) extends Judgment {
    override def toString = s"⊢ File ${typeColor(shortString(s))}"
  }

  case class NodeTree[T](node: T, children: List[NodeTree[T]])

  def mkString(l: List[String], s: String): String = l match {
    case Nil() => ""
    case Cons(x, Nil()) => x
    case Cons(x, xs) => x + s + mkString(xs, s)
  }

  def prettyPrint(l: List[NodeTree[Judgment]], depth: Int): String = {
    "<ul style='list-style-type: none;'>\n" +
      mkString(l.map(t => prettyPrint(t, depth + 1)), "\n") +
    "</ul>"
  }

  def prettyPrint(t: NodeTree[Judgment], depth: Int): String = {
    val indentation = "  " * depth
    val childrenString = prettyPrint(t.children, depth + 1)
    indentation + s"<li> <span title='${t.node.c.toString()}'> ${t.node.toString} </span>\n" +
      childrenString +
    indentation + "</li>"
  }

  def makeHTMLFile(fileName: String, trees: List[NodeTree[Judgment]]): Unit = {
    val fw = new FileWriter(fileName)
    fw.write("<!DOCTYPE html>")
    fw.write("<html lang=\"en\">")
    fw.write("<head>\n")
    fw.write("<meta charset=\"UTF-8\">\n")
    fw.write("<meta http-equiv=\"refresh\" content=\"1\"/>\n")
    fw.write("</head>\n\n")
    fw.write("<body>\n")
    fw.write(prettyPrint(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
  }
}
