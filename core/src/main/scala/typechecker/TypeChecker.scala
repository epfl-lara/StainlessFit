/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import trees._
import util.RunContext
import parser.FitParser

import Derivation._

class TypeChecker(implicit val rc: RunContext)
  extends ProvenRules
  with UnprovenRules
  with UnsoundRules
  with SMTRules
  with ControlRules
  with MetaRules {

  val deterministicTypeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CheckBool.t || CheckNat.t || CheckUnit.t || CheckVar.t ||
    CheckIf.t || CheckMatch.t || CheckEitherMatch.t || CheckLet.t ||
    CheckLeft.t || CheckRight.t || CheckSum.t ||
    CheckIntersection.t ||
    CheckLambda.t || // CheckPi.t ||
    CheckPair.t || CheckSigma.t ||
    CheckRefinement.t || CheckTypeAbs.t ||
    CheckRecursive.t ||
    CheckTop1.t || CheckTop2.t ||
    CheckReflexiveSubtype.t ||
    InferMacroTypeDecl.t ||
    InferBool.t || InferNat.t || InferUnit.t || InferVar.t ||
    InferLeft.t || InferRight.t ||
    InferSize.t ||
    InferError.t ||
    InferLet.t ||
    InferPair.t || InferFirst.t || InferSecond.t ||
    InferApp.t || InferLambda.t || InferErasableLambda.t || InferForallInstantiation.t ||
    InferTypeAbs.t || InferTypeApp.t ||
    InferBinaryPrimitive.t || InferUnaryPrimitive.t ||
    InferIf.t || InferMatch.t || InferEitherMatch.t ||
    InferFix.t ||
    InferFold.t || InferUnfold.t || InferUnfoldPositive.t || InferFoldGen.t ||
    SubtypeSigma.t || SubtypePi.t || SubtypeTop.t || SubtypeBottom.t || SubtypeReflexive.t ||
    SubtypeForall.t || SubtypeRecursive.t || 
    SubtypeRefinementRight.t || SubtypeRefinementDrop.t

  val solveEquality: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    Reflexivity.t ||
    EqualityInContext.t ||
    Z3ArithmeticSolver.t ||
    TopIf.t ||
    TopMatch.t ||
    TopEitherMatch.t ||
    NatEqualToEqual.t ||
    DestructPair.t ||
    ExpandSize.t ||
    UnfoldRefinementInContext.t ||
    PartialEval.t ||
    InlineApplications.t ||
    ExpandVars.t

  val control: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    FailRule.t

  val tactic = (deterministicTypeChecking || solveEquality || control).repeat

  def infer(t: Tree) = {
    val g = InferGoal(Context.empty, t)
    tactic.apply(g, sg => None)
  }
}

object TypeChecker {
  def debugs(g: Goal, ruleName: String)(implicit rc: RunContext) = {
    ruleNameDebug(s"${"   " * g.c.level}$ruleName")
    typeCheckDebug(s"${"   " * g.c.level}Current goal ${g} $ruleName : ${g.c.toString.replaceAll("\n", s"\n${"   " * g.c.level}")}\n")
  }

  def ruleNameDebug(s: => String)(implicit rc: RunContext): Unit = {
    if (rc.debugEnabled(DebugSection.Rule)) {
      rc.reporter.debug(s)
    }
  }

  def typeCheckDebug(s: => String)(implicit rc: RunContext): Unit = {
    if (rc.debugEnabled(DebugSection.TypeCheck)) {
      rc.reporter.debug(s)
    }
  }

  def equalityDebug(s: => String)(implicit rc: RunContext): Unit = {
    if (rc.debugEnabled(DebugSection.Equality)) {
      rc.reporter.debug(s)
    }
  }
}
