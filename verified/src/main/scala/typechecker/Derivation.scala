package typechecker

import java.io.FileWriter
import java.io.File

import _root_.trees._
import _root_.interpreter._

import stainless.collection._
import stainless.lang._

object Derivation {

  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)
  def headerColor(s: String) = color("#002875", s)
  def bold(s: String) = s"<b>$s</b>"

  sealed abstract class Judgment {
    val c: Context
    val name: String
  }

  def shortString(s: String, maxWidth: Int = 160): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  case class CheckJudgment(override val name: String, override val c: Context, e: Tree, t: Tree) extends Judgment {
    override def toString =
      s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ ${termColor(shortString(e.toString))} ⇓ ${typeColor(shortString(t.toString))}"
  }

  case class InferJudgment(override val name: String, override val c: Context, e: Tree, t: Tree) extends Judgment {
    override def toString = {
      s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ ${termColor(shortString(e.toString))} ⇑ ${typeColor(shortString(t.toString))}"
    }
  }

  case class AreEqualJudgment(override val name: String, override val c: Context, t1: Tree, t2: Tree, s: String) extends Judgment {
    override def toString = {
      s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ ${typeColor(shortString(t1.toString))} ≡ ${typeColor(shortString(t2.toString))} ${bold(s)}"
    }
  }

  case class ErrorJudgment(override val name: String, override val c: Context, error: String) extends Judgment {
    override def toString = s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ ${bold("error: " + error)}"
  }

  case class SynthesisJudgment(override val name: String, override val c: Context, tp: Tree, t: Tree) extends Judgment {
    override def toString = {
      s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ ${typeColor(shortString(t.toString))} ⇐ ${typeColor(shortString(tp.toString))}"
    }
  }

  case class EmptyJudgment(override val name: String, override val c: Context) extends Judgment {
    override def toString = ""
  }

  case class FileJudgment(override val name: String, override val c: Context, s: String) extends Judgment {
    override def toString = s"(${headerColor(c.level.toString)} - ${headerColor(name)}) ⊢ File ${typeColor(shortString(s))}"
  }

  case class NodeTree[T](node: T, children: List[NodeTree[T]])

  def mkString(l: List[String], s: String): String = l match {
    case Nil() => ""
    case Cons(x, Nil()) => x
    case Cons(x, xs) => x + s + mkString(xs, s)
  }

  def prettyPrint(l: List[NodeTree[Judgment]], depth: Int): String = {
    val indentation = "  " * depth
    indentation + "<ul style='list-style-type: none;'>\n" +
      mkString(l.map(t => prettyPrint(t, depth + 1)), "\n") + "\n" +
    indentation + "</ul>"
  }

  def prettyPrint(t: NodeTree[Judgment], depth: Int): String = {
    val indentation = "  " * depth
    val childrenString = prettyPrint(t.children, depth + 1)
    indentation + s"<li> <span class='node' title='${t.node.c.toString()}'> ${t.node.toString} </span>\n" +
      childrenString + "\n" +
    indentation + "</li>"
  }

  def makeHTMLFile(file: File, trees: List[NodeTree[Judgment]], success: Boolean): Unit = {
    val htmlFile = new File(file.getAbsolutePath() + ".html")
    val fw = new FileWriter(htmlFile)
    val status = if (success) "Success" else "Failed"
    val name = file.getName()
    fw.write("<!DOCTYPE html>")
    fw.write("<html lang=\"en\">")
    fw.write("<head>\n")
    fw.write("<meta charset=\"UTF-8\">\n")
    // fw.write("<meta http-equiv=\"refresh\" content=\"1\"/>\n")
    fw.write(s"<title> Type Checking File $name: $status </title>\n")
    fw.write("<style>body { font-family: \"Fira Code\", Menlo, Monaco, monospace }</style>\n")
    fw.write("</head>\n\n")
    fw.write("<body>\n")
    fw.write("""<script type="text/javascript" src="https://ajax.googleapis.com/ajax/libs/jquery/3.1.0/jquery.min.js"></script>""")
    fw.write("<script>\n")
    fw.write("""|$(document).ready(function () {
                |  $('.node').click(function(e) {
                |    text = $(this).html()
                |    if (text.startsWith("(Folded) "))
                |      $(this).html(text.substring(9));
                |    else
                |      $(this).html("(Folded) " + text);
                |    $(this).parent().find("ul").slideToggle(100);
                |  });
                |});
                |""".stripMargin)
    fw.write("</script>\n")
    fw.write(s"<h1> Type Checking File $name: $status </h1>\n")
    fw.write(prettyPrint(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
  }
}
