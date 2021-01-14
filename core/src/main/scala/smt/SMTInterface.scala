/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package smt

import core.util.RunContext

import java.io.{File, PrintWriter, Writer}

import smtlib.printer.RecursivePrinter
import smtlib.theories.Core.{BoolSort, And => TermAnd, Equals => TermEquals, Not => TermNot, Or => TermOr}
import smtlib.theories.Ints.{Div => TermDiv, Mul => TermMul, _}
import smtlib.trees.Commands._
import smtlib.trees.Terms.{QualifiedIdentifier, SNumeral, SSymbol, SimpleIdentifier, Sort, Term}
import fit.core.trees._

import scala.language.postfixOps
import scala.sys.process._

class SMTInterface(path: String) {
  private val writer = new SMTWriter(path)
  private val declaredVariables: scala.collection.mutable.Map[Tree, Term] = scala.collection.mutable.Map()
  private var variableToType: Map[Tree, Tree] = Map()
  private var satisfiable: Option[Boolean] = None

  def declareVariables(subtrees: Map[Tree, Tree]): Unit = {
    variableToType = variableToType ++ subtrees
    subtrees.foreachEntry(declareVar)
  }

  def addAssertions(assertions: Seq[Tree]): Unit =
    assertions.foreach(addAssertion)

  def addAssertion(t: Tree): Unit = {
    writer.addAssertion(treeToTerm(t, BoolType).get)
  }

  // TODO: refactor this
  def isSatisfiable: Boolean = {
    if (satisfiable.isDefined)
      satisfiable.get
    else {
      writer.close()

      val solverInput = scala.io.Source.fromFile(path).mkString

      val cmd = s"""z3 dump-models=true "$path""""
      var output = ""
      val code = cmd ! ProcessLogger(s => {
        output += s + "\n"
      })
      if (code != 0)
        throw new Exception(s"Error (code $code) in Z3:\n$output")
      else if (output.contains("unsat")) {
        satisfiable = Some(false)
        false
      }
      else {
      // TODO: logging
        satisfiable = Some(true)
        true
      }
    }
  }

  private def treeToTerm(tree: Tree, typ: Tree): Option[Term] = {
    tree match {
      case BooleanLiteral(false) => Some(t("false"))
      case BooleanLiteral(true) => Some(t("true"))
      case NatLiteral(i) => Some(SNumeral(i))
      case Primitive(op @ (Eq | Neq), t1 :: t2 :: Nil) =>
        val e1 = treeToTerm(t1, BoolType) orElse treeToTerm(t1, NatType)
        val e2 = treeToTerm(t2, BoolType) orElse treeToTerm(t2, NatType)
        e1.flatMap(l => e2.map(r => op match {
          case Eq => TermEquals(l, r)
          case Neq => TermNot(TermEquals(l, r))
          case _ => ??? // unreachable
        })) orElse Some(declaredVariables(tree))
      case Primitive(op, t1 :: t2 :: Nil) if op.isNatBinOp =>
        val e1 = treeToTerm(t1, NatType).get
        val e2 = treeToTerm(t2, NatType).get
        Some(op match {
          case Plus => Add(e1, e2)
          case Minus => Sub(e1, e2)
          case Mul => TermMul(e1, e2)
          case Div => TermDiv(e1, e2)
          case Leq => LessEquals(e1, e2)
          case Geq => GreaterEquals(e1, e2)
          case Lt => LessThan(e1, e2)
          case Gt => GreaterThan(e1, e2)
          case _ => throw new UnsupportedOperationException(s"Expected a NatBinOp, got $op")
        })
      case Primitive(op, t1 :: t2 :: Nil) if op.isBoolToBoolBinOp =>
        val e1 = treeToTerm(t1, NatType).get
        val e2 = treeToTerm(t2, NatType).get
        Some(op match {
          case And => TermAnd(e1, e2)
          case Or => TermOr(e1, e2)
          case _ => throw new UnsupportedOperationException(s"Expected a BoolBinOp, got $op")
        })
      case Primitive(op, t1 :: Nil) if op.isBoolToBoolUnOp =>
        val term = treeToTerm(t1, BoolType).get
        Some(op match {
          case Not => TermNot(term)
          case _ => throw new UnsupportedOperationException(s"Expected a BoolToBoolUnOp, got $op")
        })
      case _ =>
        if (variableToType.get(tree).contains(typ))
          Some(declaredVariables(tree))
        else
          None
    }
  }

  private def declareVar(tree: Tree, tp: Tree): Term = {
    if (!declaredVariables.contains(tree)) {
      val id = fit.core.trees.Identifier.fresh("solverVar").uniqueString
      declaredVariables(tree) = t(id)
      tp match {
        case BoolType =>
          writer.declareVar(id, BoolSort())
        case NatType =>
          writer.declareVar(id, IntSort())
          writer.addAssertion(GreaterEquals(t(id), SNumeral(0)))
        case _ => throw new UnsupportedOperationException("Only variables of Bool and Nat type are supported")
      }
    }
    declaredVariables(tree)
  }

  private def t(s: String): Term = QualifiedIdentifier(SimpleIdentifier(SSymbol(s)))
}

class SMTWriter(path: String) {
  def declareVar(id: String, sort: Sort): Unit =
    pc(DeclareConst(SSymbol(id), sort), writer)

  def addAssertion(t: Term): Unit =
    pc(Assert(t), writer)

  def close(): Unit = {
    pc(CheckSat(), writer)
    writer.close()
  }

  private def pc(c: Command, w: Writer): Unit = RecursivePrinter.printCommand(c, w)

  private val file = new File(path)
  if (!file.getParentFile.exists()) file.getParentFile.mkdirs()
  if (!file.exists()) file.createNewFile()
  private val writer = new PrintWriter(file)
}
