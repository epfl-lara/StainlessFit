/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package typechecker

case class Tactic[A,B](apply: (A, (A => Option[B])) => Option[B]) {
  def ||(other: Tactic[A,B]): Tactic[A,B] = this.or(other)
  def or(other: Tactic[A,B]): Tactic[A,B] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, subgoalSolver) orElse
        other.apply(g, subgoalSolver)
    }

  def orRecover(other: Tactic[A,B]): Tactic[A,B] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, subgoalSolver) match {
          case result @ Some((true, _)) => result
          case _ => other.apply(g, subgoalSolver)
        }
    }

  def andThen(other: Tactic[A,B]): Tactic[A,B] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, sg => other.apply(sg, subgoalSolver))
    }

  def repeat: Tactic[A,B] = {
    def repeatApply(goal: A, subgoalSolver: A => Option[B]): Option[B] = {
      apply(goal, sg => repeatApply(sg, subgoalSolver))
    }
    Tactic[A,B](repeatApply)
  }
}
