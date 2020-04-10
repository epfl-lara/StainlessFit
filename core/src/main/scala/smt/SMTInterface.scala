package stainlessfit
package core

import java.io.{File, Writer}

import smtlib.printer.RecursivePrinter
import smtlib.theories.Core.{And => TermAnd, Equals => TermEquals, Not => TermNot, Or => TermOr}
import smtlib.theories.Ints.{Div => TermDiv, Mul => TermMul, _}
import smtlib.trees.Commands._
import smtlib.trees.Terms._
import stainlessfit.core.trees._

import scala.language.postfixOps
import scala.sys.process._

object SMTInterface {
  def declareVar(id: String, w: Writer): Unit =
    pc(DeclareConst(sy(id), IntSort()), w)

  def addAssertion(t: Tree, w: Writer): Unit =
    pc(Assert(treeToTerm(t)), w)

  def isSatisfiable(file: File, w: Writer): Boolean = {
    pc(CheckSat(), w)
    w.close()

    val cmd = s"""z3 dump-models=true "${file.getPath}""""
    var output = ""
    val code = cmd ! ProcessLogger(s => {
      output += s + "\n"
    })
    if (code != 0)
      throw new Exception(s"Error (code $code) in Z3:\n$output")
    else if (output.contains("unsat")) false
    else
    // TODO: logging
      true
  }

  private def pc(c: Command, w: Writer): Unit = RecursivePrinter.printCommand(c, w)

  def sy(s: String) = SSymbol(s)

  def si(s: SSymbol) = SimpleIdentifier(s)

  def t(s: SSymbol): QualifiedIdentifier = QualifiedIdentifier(si(s))

  def t(s: String): Term = t(sy(s))

  def treeToTerm(tree: Tree): Term =
    tree match {
      case Var(id) => t(id.toString)
      case BooleanLiteral(false) => t("false")
      case BooleanLiteral(true) => t("true")
      case NatLiteral(i) => SNumeral(i)
      case Primitive(op, args) =>
        val e1: Option[Term] = args match {
          case head :: _ => Some(treeToTerm(head))
          case Nil => None
        }
        val e2: Option[Term] = args match {
          case _ :: second :: _ => Some(treeToTerm(second))
          case _ => None
        }
        op match {
          case Not => TermNot(e1.get)
          case And => TermAnd(e1.get, e2.get)
          case Or => TermOr(e1.get, e2.get)
          case Plus => Add(e1.get, e2.get)
          case Minus => Sub(e1.get, e2.get)
          case Mul => TermMul(e1.get, e2.get)
          case Div => TermDiv(e1.get, e2.get)
          case Eq => TermEquals(e1.get, e2.get)
          case Neq => TermNot(TermEquals(e1.get, e2.get))
          case Leq => LessEquals(e1.get, e2.get)
          case Geq => GreaterEquals(e1.get, e2.get)
          case Lt => LessThan(e1.get, e2.get)
          case Gt => GreaterThan(e1.get, e2.get)
          case Nop => e1.get
        }
    }
}
