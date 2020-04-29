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

  def typeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    ContextSanity.t ||
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
    InferNatMatch1.t ||
    InferListMatch.t ||
    CheckInfer.t ||
    NormBase.t ||
    NormSingleton.t ||
    NormExists1.t ||
    NormExists2.t ||
    NormNatMatch.t ||
    NormListMatch.t ||
    NormCons.t ||
    NormPi.t ||
    NormSigma.t ||
    SubNormalize.t ||
    SubExistsLeft.t ||
    SubExistsRight.t ||
    SubNatMatch.t ||
    SubListMatch.t ||
    SubSigma.t ||
    SubCons1.t ||
    SubCons2.t ||
    SubPi.t ||
    SubSingletonReflexive.t ||
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

class ScalaDepSolver(var targets: Map[Identifier, Option[Tree]])(implicit rc: RunContext) extends ScalaDep with Tree.Solver {
  def SubReflexiveSolve = Rule("SubReflexiveSolve", {
    case g @ SubtypeGoal(c, ty1, ty2) if Tree.areEqual(ty1, ty2)(rc, this) =>
      TypeChecker.debugs(g, "SubReflexiveSolve")
      Some((List(), _ => (true, SubtypeJudgment("SubReflexiveSolve", c, ty1, ty2))))
    case g =>
      None
  })

  override def typeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    SubReflexiveSolve.t || super.typeChecking

  def addTarget(x: Identifier): Unit = {
    assert(!targets.contains(x))
    targets += x -> None
  }

  def recordSolution(x: Identifier, tSol: Tree): Unit = {
    assert(targets.contains(x))
    if (targets(x) == None)
      targets += x -> Some(tSol)
  }

  def solve(c: Context, ty1: Tree, ty2: Tree) = {
    val g = SubtypeGoal(c, ty1, ty2)
    tactic.apply(g, sg => None)
  }
}
