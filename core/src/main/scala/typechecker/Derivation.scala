package core
package typechecker

import java.io.FileWriter
import java.io.File

import core.trees._
import core.interpreter._

import Formatting._

object Derivation {

  sealed abstract class Judgment {
    val context: Context
    val name: String
  }

  case class CheckJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment {
    override def toString =
      "<span class='check'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termColor(shortString(e.toString)) + " ⇓ " +
        typeColor(shortString(t.toString)) +
      "</span>"
  }

  case class InferJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment {
    override def toString = {
      "<span class='infer'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termColor(shortString(e.toString)) + " ⇑ " +
        typeColor(shortString(t.toString)) +
      "</span>"
    }
  }

  case class AreEqualJudgment(override val name: String, override val context: Context, t1: Tree, t2: Tree, s: String) extends Judgment {
    override def toString = {
      "<span class='equal'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termColor(shortString(t1.toString)) + " ≡ " +
        termColor(shortString(t2.toString)) +
      "</span>"
    }
  }

  case class ErrorJudgment(override val name: String, override val context: Context, error: String) extends Judgment {
    override def toString = s"(${headerColor(context.level.toString)} - ${headerColor(name)}) ⊢ ${bold("error: " + error)}"
  }

  case class SynthesisJudgment(override val name: String, override val context: Context, tp: Tree, t: Tree) extends Judgment {
    override def toString = {
      s"(${headerColor(context.level.toString)} - ${headerColor(name)}) ⊢ ${typeColor(shortString(t.toString))} ⇐ ${typeColor(shortString(tp.toString))}"
    }
  }

  case class EmptyJudgment(override val name: String, override val context: Context) extends Judgment {
    override def toString = ""
  }

  case class FileJudgment(override val name: String, override val context: Context, s: String) extends Judgment {
    override def toString = s"(${headerColor(context.level.toString)} - ${headerColor(name)}) ⊢ File ${typeColor(shortString(s))}"
  }

  case class NodeTree[T](node: T, children: List[NodeTree[T]])

  def mkString(l: List[String], s: String): String = l match {
    case Nil => ""
    case x ::  Nil => x
    case x ::  xs => x + s + mkString(xs, s)
  }

  def prettyPrint(l: List[NodeTree[Judgment]], depth: Int): String = {
    val indentation = "  " * depth
    indentation + "<ul>\n" +
      l.map(t => prettyPrint(t, depth + 1)).mkString("\n") + "\n" +
    indentation + "</ul>"
  }

  def prettyPrint(t: NodeTree[Judgment], depth: Int): String = {
    val indentation = "  " * depth
    val childrenString = prettyPrint(t.children, depth + 1)
    indentation + s"<li> <span class='node' title='${t.node.context.toString}'> ${t.node.toString} </span>\n" +
      childrenString + "\n" +
    indentation + "</li>"
  }

  def makeHTMLFile(reporter: Reporter, file: File, trees: List[NodeTree[Judgment]], success: Boolean): Unit = {
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
    fw.write("""|<style>
                |body {
                |  font-family: "Fira Code", Menlo, Monaco, monospace
                |}
                |
                |.infer {
                |  background-color: #f0f0ff
                |}
                |
                |.infer:hover {
                |  background-color: #e0e0ee
                |}
                |
                |.check {
                |  background-color: #f0fff0
                |}
                |
                |.check:hover {
                |  background-color: #e0eee0
                |}
                |
                |.equal {
                |  background-color: #feffc2
                |}
                |
                |.equal:hover {
                |  background-color: #dadba7
                |}
                |
                |ul {
                |  list-style-type: none;
                |  padding-left: 10px;
                |}
                |</style>""".stripMargin)
    fw.write("</head>\n\n")
    fw.write("<body>\n")
    fw.write("""<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.min.js"></script>""")
    fw.write("<script>\n")
    fw.write("""|$(document).ready(function () {
                |  $('.node').click(function(e) {
                |    if (!getSelection().toString()) {
                |      text = $(this).html()
                |      if (text.startsWith("(Folded) "))
                |        $(this).html(text.substring(9));
                |      else
                |        $(this).html("(Folded) " + text);
                |      $(this).parent().find("ul").toggle();
                |    }
                |  });
                |});
                |""".stripMargin)
    fw.write("</script>\n")
    fw.write(s"<h1> Type Checking File $name: $status </h1>\n")
    fw.write(prettyPrint(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
    reporter.info(s"Created HTML file with derivations in: $htmlFile")
  }
}
