package stainlessfit
package core
package typechecker

import trees._
import util.RunContext
import parser.FitParser

import Derivation._


object Context {
  def empty(implicit rc: RunContext): Context = Context(Map(), Set(), 0, 0)
  def empty(max: Int)(implicit rc: RunContext): Context = Context(Map(), Set(), 0, max)
}

case class Context(
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Identifier],
  val level: Int,
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
)(implicit rc: RunContext) extends Positioned {

  def bind(i: Identifier, t: Tree): Context = {
    if (termVariables.contains(i)) throw new Exception("Already bound " + i.toString)
    copy(
      termVariables = termVariables.updated(i, t)
    )
  }

  def addTypeVariable(i: Identifier): Context = copy(typeVariables = typeVariables + i)

  def bindFresh(s: String, t: Tree): (Identifier, Context) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def getFresh(s: String): (Identifier, Context) = (Identifier(n, s), copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree): Context = bindFresh("eq", EqualityType(t1, t2))._2

  def incrementLevel: Context = copy(level = level + 1)

  def containsVarOfType(tp: Tree): Boolean =
    termVariables.exists(_._2 == tp)

  def getVarOfType(tp: Tree): Option[Identifier] =
    termVariables.find(_._2 == tp).map(_._1)

  override def toString: String = {
    Printer.asString(this)(rc)
  }

  def hasRefinement: Boolean = {
    termVariables.exists { case (v, tp) =>
      tp match {
        case RefinementType(_, _) => true
        case _ => false
      }
    }
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Context = {
    copy(
      termVariables = termVariables.map {
        case (v, tp) => (v, tp.replace(id, t))
      }
    )
  }
}

case class Tactic[A,B](apply: (A, (A => Option[B])) => Option[B]) {
  def ||(other: Tactic[A,B]): Tactic[A,B] = this.or(other)
  def or(other: Tactic[A,B]): Tactic[A,B] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, subgoalSolver) orElse
        other.apply(g, subgoalSolver)
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

class TypeChecker(implicit val rc: RunContext)
  extends TypeCheckerProvenRules
  with TypeCheckerUnprovenRules
  with TypeCheckerUnsoundRules
  with TypeCheckerSMTRules
  with TypeCheckerControlRules
  with TypeCheckerMetaRules {

  val deterministicTypeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CheckBool.t || CheckNat.t || CheckUnit.t || CheckVar.t ||
    CheckIf.t || CheckMatch.t || CheckEitherMatch.t || CheckLet.t ||
    CheckLeft.t || CheckRight.t || CheckSum.t ||
    CheckIntersection.t ||
    CheckLambda.t || CheckPi.t ||
    CheckPair.t || CheckSigma.t ||
    CheckRefinement.t || CheckTypeAbs.t ||
    CheckRecursive.t ||
    CheckTop1.t || CheckTop2.t ||
    CheckReflexive.t ||
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
    InferFold.t || InferUnfold.t || InferUnfoldPositive.t || InferFoldGen.t

  val solveEquality: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    Reflexivity.t ||
    EqualityInContext.t ||
    UnsoundIgnoreEquality.t
    // Z3ArithmeticSolver.t ||
    // ExpandVars.t ||
    // TopIf.t ||
    // TopMatch.t ||
    // NatEqualToEqual.t ||
    // UnfoldRefinementInContext.t ||
    // InlineApplications.t ||

  val control: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    FailRule.t

  val tactic = (deterministicTypeChecking || solveEquality || control).repeat

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context.empty(max), t)
    tactic.apply(g, sg => None)
  }
}

object TypeChecker {
  def debugs(rc: RunContext, g: Goal, ruleName: String) = {
    ruleNameDebug(rc, s"${"   " * g.c.level}$ruleName")
    typeCheckDebug(rc, s"${"   " * g.c.level}Current goal ${g} $ruleName : ${g.c.toString.replaceAll("\n", s"\n${"   " * g.c.level}")}\n")
  }

  def ruleNameDebug(rc: RunContext, s: => String): Unit = {
    if (rc.debugEnabled(DebugSection.Rule)) {
      rc.reporter.debug(s)
    }
  }

  def typeCheckDebug(rc: RunContext, s: => String): Unit = {
    if (rc.debugEnabled(DebugSection.TypeCheck)) {
      rc.reporter.debug(s)
    }
  }

  def equalityDebug(rc: RunContext, s: => String): Unit = {
    if (rc.debugEnabled(DebugSection.Equality)) {
      rc.reporter.debug(s)
    }
  }
}
