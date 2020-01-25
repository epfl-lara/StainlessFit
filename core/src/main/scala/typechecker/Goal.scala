package core
package typechecker

import trees._


sealed abstract class Goal {
  val c: Context

  def replace(id: Identifier, t: Tree): Goal

  def updateContext(c: Context): Goal
}

case class InferGoal(c: Context, t: Tree) extends Goal {
  override def toString: String = {
    s"Inferring $t"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    InferGoal(c.replace(id, t1), t.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${t}: ${tp}"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    CheckGoal(c.replace(id, t1), t.replace(id, t1), tp.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class SynthesisGoal(c: Context, tp: Tree) extends Goal {
  def replace(id: Identifier, t: Tree): Goal = {
    SynthesisGoal(c.replace(id, t), tp.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EqualityGoal(c: Context, t1: Tree, t2: Tree) extends Goal {
  override def toString: String = {
    s"Check equality ${t1} ≡ ${t2}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EqualityGoal(c.replace(id, t), t1.replace(id, t), t2.replace(id, t))
  }

  def updateContext(newC: Context): Goal = {
    copy(c = newC)
  }
}

case class ErrorGoal(c: Context, s: String) extends Goal {
  val level = 0

  override def toString: String = {
    s"Error Goal: ${s}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    ErrorGoal(c.replace(id, t), s)
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EmptyGoal(c: Context) extends Goal {

  override def toString: String = {
    s"No Goal"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EmptyGoal(c.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}
