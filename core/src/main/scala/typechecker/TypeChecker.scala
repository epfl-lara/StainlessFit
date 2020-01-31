package core
package typechecker

import core.trees._

import Derivation._

object Context {
  def empty: Context = Context(List(), Map(), Set(), 0, 0)
  def empty(max: Int): Context = Context(List(), Map(), Set(), 0, max)
}

case class Context(
  val variables: List[Identifier],
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Identifier],
  val level: Int,
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
) {

  def bind(i: Identifier, t: Tree): Context = {
    if (variables.contains(i)) throw new Exception("Already bound " + i.toString)
    copy(
      termVariables = termVariables.updated(i, t),
      variables = i :: variables
    )
  }

  def addTypeVariable(i: Identifier): Context = copy(typeVariables = typeVariables + i)

  def bindFresh(s: String, t: Tree): (Identifier, Context) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def getFresh(s: String): (Identifier, Context) = (Identifier(n, s), copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree): Context = bindFresh("eq", EqualityType(t1, t2))._2

  def incrementLevel(): Context = copy(level = level + 1)

  def containsVarOfType(tp: Tree): Boolean =
    variables.exists(v => termVariables.contains(v) && termVariables(v) == tp)

  def getVarOfType(tp: Tree): Option[Identifier] =
    variables.find(v => termVariables.contains(v) && termVariables(v) == tp)

  override def toString: String = {
    "Term variables:\n" ++
    variables.foldLeft("") {
      case (acc, id) => acc + s"${id}: ${termVariables(id)}\n"
    }
  }

  def hasRefinementBound: Boolean = {
    variables.exists { case v =>
      termVariables.contains(v) &&
      (termVariables(v) match {
        case RefinementType(_, _) => true
        case _ => false
      })
    }
  }

  def replace(id: Identifier, t: Tree): Context = {
    copy(
      termVariables = variables.foldLeft(Map[Identifier, Tree]()) {
        case (m, termId) =>
          if (termVariables.contains(termId))
            m.updated(termId, Tree.replace(id, t, termVariables(termId)))
          else
            m
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

object TypeChecker {
  import TypeCheckerProvenRules._
  import TypeCheckerUnprovenRules._
  import TypeCheckerUnsoundRules._
  import TypeCheckerSMTRules._
  import TypeCheckerControlRules._
  import TypeCheckerMetaRules._

  val deterministicTypeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CheckBool.t || CheckNat.t || CheckUnit.t || CheckVar.t || CheckIf.t ||
    CheckMatch.t || CheckEitherMatch.t || CheckLet.t ||
    CheckLeft.t || CheckRight.t ||
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

  val tdebug = false
  val edebug = false
  val zdebug = false
  val ndebug = false

  val tactic = (deterministicTypeChecking || solveEquality || control).repeat

  def infer(t: Tree, max: Int) = {
    // println("Type-Checking")
    // println(t)
    val g = InferGoal(Context.empty(max), t)
    tactic.apply(g, sg => None)
  }

  def debugs(g: Goal, ruleName: String) = {
    TypeChecker.ruleNameDebug(s"${"   " * g.c.level}$ruleName")
    TypeChecker.typeCheckDebug(s"${"   " * g.c.level}Current goal ${g} $ruleName : ${g.c.toString.replaceAll("\n", s"\n${"   " * g.c.level}")}\n")
  }

  def ruleNameDebug(s: String): Unit = {
    if (ndebug) println(s)
  }

  def typeCheckDebug(s: String): Unit = {
    if (tdebug) println(s)
  }

  def equalityDebug(s: String): Unit = {
    if (edebug) println(s)
  }

  def z3Debug(s: String): Unit = {
    if (zdebug) println(s)
  }
}
