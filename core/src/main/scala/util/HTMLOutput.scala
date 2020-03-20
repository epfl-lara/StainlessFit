package stainlessfit
package core
package util

import core.trees._
import core.typechecker.Derivation._
import core.typechecker._

import java.io.FileWriter
import java.io.File
import core.typechecker.EmptyGoal

object HTMLOutput {
  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)
  def headerColor(s: String) = color("#002875", s)
  def bold(s: String) = s"<b>$s</b>"

  def shortString(s: String, maxWidth: Int = 90): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  def termOutput(t: Tree)(implicit rc: RunContext): String =
    termColor(shortString(Printer.exprAsString(t)))

  def typeOutput(t: Tree)(implicit rc: RunContext): String =
    typeColor(shortString(Printer.typeAsString(t)))

  def goalToHTML(g: Goal)(implicit rc: RunContext): String = g match {
    case EmptyGoal(_) => ""
    case ErrorGoal(_, _) => ""
    case InferGoal(c, t) => termOutput(t) + " ⇑ _"
    case CheckGoal(c, t, tp) => termOutput(t) + " ⇓ " + typeOutput(tp)
    case SubtypeGoal(c, ty1, ty2) => typeOutput(ty1) + " <: " + typeOutput(ty2)
    case SynthesisGoal(c, tp) =>
      s"_ ⇐ ${typeOutput(tp)}"
    case EqualityGoal(c, t1, t2) =>
      termOutput(t1)+ " ≡ " + termOutput(t2)
  }

  def judgementToHTML(j: Judgment)(implicit rc: RunContext): String = j match {
    case CheckJudgment(name, context, t, tp) =>
      "<span class='check'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termOutput(t) + " ⇓ " + typeOutput(tp) +
      "</span>"

    case SubtypeJudgment(name, context, ty1, ty2) =>
      "<span class='check'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        typeOutput(ty1) + " <: " + typeOutput(ty2) +
      "</span>"

    case InferJudgment(name, context, t, tp) =>
      "<span class='infer'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termOutput(t) + " ⇑ " + typeOutput(tp) +
      "</span>"

    case AreEqualJudgment(name, context, t1, t2, _) =>
      "<span class='equal'>" +
        "(" + headerColor(context.level.toString) + " - " + headerColor(name) + ") ⊢ " +
        termOutput(t1) + " ≡ " + termOutput(t2) +
      "</span>"

    case SynthesisJudgment(name, context, tp, t) =>
      s"(${headerColor(context.level.toString)} - ${headerColor(name)}) ⊢ ${typeColor(shortString(t.toString))} ⇐ ${typeOutput(tp)}"

    case ErrorJudgment(name, goal, errOpt) =>
      val errorString = errOpt.map(err => s" [ERROR: $err]").mkString
      "<span class='error'>" +
      "(" + headerColor(goal.c.level.toString) + " - " + headerColor(name) + ") ⊢ " +
      goalToHTML(goal) + errorString +
      "</span>"

    case EmptyJudgment(name, context) =>
      s""

    case FileJudgment(name, context, s) =>
      s"(${headerColor(context.level.toString)} - ${headerColor(name)}) ⊢ File ${typeColor(shortString(s))}"
  }

  def nodeTreeToHTML(l: List[NodeTree[Judgment]], depth: Int)(implicit rc: RunContext): String = {
    val indentation = "  " * depth
    indentation + "<ul>\n" +
      l.map(t => nodeTreeToHTML(t, depth + 1)).mkString("\n") + "\n" +
    indentation + "</ul>"
  }

  def nodeTreeToHTML(t: NodeTree[Judgment], depth: Int)(implicit rc: RunContext): String = {
    val indentation = "  " * depth
    val childrenString = nodeTreeToHTML(t.children, depth + 1)
    indentation + s"<li> <span class='node' title='${Printer.asString(t.node.context)}'> ${judgementToHTML(t.node)} </span>\n" +
      childrenString + "\n" +
    indentation + "</li>"
  }

  def makeHTMLFile(file: File, trees: List[NodeTree[Judgment]], success: Boolean)(implicit rc: RunContext): Unit = {
    val htmlFile = new File(file.getAbsolutePath() + ".html")
    val fw = new FileWriter(htmlFile)
    val status = if (success) "Success" else "Failed"
    val name = file.getName()
    fw.write("<!DOCTYPE html>")
    fw.write("<html lang=\"en\">")
    fw.write("<head>\n")
    fw.write("<meta charset=\"UTF-8\">\n")
    if (rc.config.refresh > 0)
      fw.write(s"<meta http-equiv='refresh' content='${rc.config.refresh}' />\n")
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
                |.error {
                |  background-color: #ffbcab
                |}
                |
                |.error:hover {
                |  background-color: #cc9587
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
    fw.write(nodeTreeToHTML(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
    rc.reporter.info(s"Created HTML file with derivations in: $htmlFile")
  }
}
