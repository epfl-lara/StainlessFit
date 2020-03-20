package stainlessfit
package core
package typechecker

import trees._
import util.RunContext
import parser.FitParser

import Derivation._

class ScalaDep(implicit val rc: RunContext)
  extends ProvenRules
  with    ScalaDepRules
  with    ControlRules
  with    MetaRules {

  val typeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    InferVar1.t ||
    InferNat.t ||
    InferLet1.t ||
    InferLambda.t ||
    InferApp1.t

  val control: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    FailRule.t

  val tactic = (typeChecking || control).repeat

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context.empty(max), t)
    tactic.apply(g, sg => None)
  }
}
