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
    InferNat1.t ||
    InferUnit.t ||
    InferBool.t ||
    InferChoose.t ||
    InferFixWithDefault.t ||
    InferLet1.t ||
    InferLet2.t ||
    InferNil.t ||
    InferCons.t ||
    InferLambda1.t ||
    InferApp1.t ||
    InferPair1.t ||
    InferListMatch.t ||
    CheckInfer.t ||
    NormBase.t ||
    NormSingleton.t ||
    NormSubstVar.t ||
    NormExists.t ||
    NormListMatch.t ||
    NormPi.t ||
    NormSigma.t ||
    SubNormalize.t ||
    SubListMatch.t ||
    SubPi.t ||
    SubSigma.t ||
    SubReflexive.t ||
    SubSingletonLeft.t ||
    SubTop.t

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
