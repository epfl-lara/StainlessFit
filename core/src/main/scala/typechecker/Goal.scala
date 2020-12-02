/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import trees._
import util.RunContext
import parser.FitParser

sealed abstract class Goal {
  val c: Context

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal

  def updateContext(c: Context): Goal
}

case class InferGoal(c: Context, t: Tree) extends Goal {
  override def toString: String = {
    s"Inferring $t"
  }

  def replace(id: Identifier, t1: Tree)(implicit rc: RunContext): Goal = {
    InferGoal(c.replace(id, t1), t.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${t}: ${tp}"
  }

  def replace(id: Identifier, t1: Tree)(implicit rc: RunContext): Goal = {
    CheckGoal(c.replace(id, t1), t.replace(id, t1), tp.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class SubtypeGoal(c: Context, tp1: Tree, tp2: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${tp1} <: ${tp2}"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    SubtypeGoal(c.replace(id, t), tp1.replace(id, t), tp2.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class NormalizedSubtypeGoal(c: Context, tp1: Tree, tp2: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${tp1} <:‖ ${tp2}"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    NormalizedSubtypeGoal(c.replace(id, t), tp1.replace(id, t), tp2.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class NormalizationGoal(c: Context, ty: Tree) extends Goal {
  override def toString: String = {
    s"Normalizing $ty"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    // NormalizationGoal(c.replace(id, t), ty.replace(id, t))
    ???
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class SynthesisGoal(c: Context, tp: Tree) extends Goal {
  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    SynthesisGoal(c.replace(id, t), tp.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EqualityGoal(c: Context, t1: Tree, t2: Tree) extends Goal {
  override def toString: String = {
    s"Check equality ${t1} ≡ ${t2}"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    EqualityGoal(c.replace(id, t), t1.replace(id, t), t2.replace(id, t))
  }

  def updateContext(newC: Context): Goal = {
    copy(c = newC)
  }
}

case class ErrorGoal(c: Context, err: Option[String]) extends Goal {
  val level = 0

  override def toString: String = {
    s"Error Goal: ${err}"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    ErrorGoal(c.replace(id, t), err)
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EmptyGoal(c: Context) extends Goal {

  override def toString: String = {
    s"No Goal"
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Goal = {
    EmptyGoal(c.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}
