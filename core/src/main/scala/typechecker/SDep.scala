/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import trees._
import util.RunContext
import parser.FitParser

import Derivation._
import SDepSugar._

class SDep(implicit val rc: RunContext)
  extends ProvenRules
  with    SDepRules
  with    ControlRules
  with    MetaRules {

  def typeChecking: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    ContextSanity.t ||
    InferSolverVar.t ||
    InferNormalVar.t ||
    InferNat1.t ||
    InferUnit.t ||
    InferBool.t ||
    InferChoose.t ||
    InferFixWithDefault.t ||
    InferFixDep.t ||
    InferLet1.t ||
    InferLet2.t ||
    InferNil.t ||
    InferCons.t ||
    InferLambda1.t ||
    InferApp1.t ||
    InferSucc.t ||
    InferPair1.t ||
    InferNatMatch1.t ||
    InferListMatch.t ||
    InferAscribe.t ||
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
    orRecover(SubNormalizeWiden.t, SubNormalize.t) ||
    // SSubForcedMatchRightNil.t ||
    // SSubForcedMatchRightCons.t ||
    // SubSingletonCons.t ||
    SubSingletonListMatch1.t ||
    SubSingletonListMatch2.t ||
    SubSingletonReflexive.t ||
    SubReflexive.t ||
    SubExistsLeft.t ||
    // SubExistsRight.t ||
    SubNatMatch.t ||
    SubListMatch.t ||
    SubSigma.t ||
    SubCons1.t ||
    SubCons2.t ||
    SubPi.t ||
    orRecover(SSubListMatchGuessNil.t, SSubListMatchGuessCons.t) ||
    // SubSingletonLeft.t ||
    orRecover(SubSingletonLeft.t, SubExistsRight.t) ||
    SubTop.t

  // Like FailRule, but only on SubtypeGoals and doesn't report an error.
  // This way we can try alternatives in SubNormalize* without printing spurious errors.
  val SubtypeFailRule = Rule("SubtypeFailRule", {
    case g @ SubtypeGoal(_, _, _) => Some((List(), _ =>
      (false, ErrorJudgment("SubtypeFailRule", g, Some("Goal is not handled")))
    ))
    case _ => None
  })

  val control: Tactic[Goal, (Boolean, NodeTree[Judgment])] =
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    SubtypeFailRule.t ||
    FailRule.t

  val tactic = (typeChecking || control).repeat


  // === Inference === (entrypoint)

  def infer(t: Tree) = {
    val g = InferGoal(Context.empty, t)
    tactic.apply(g, sg => None)
  }


  // === Solving ===

  private var solveCount: Int = 0 // number of solve invocations
  private var solverDepth: Int = 0

  private var targets: Map[Identifier, Tree] = Map.empty // ie. unification variables
  private var solutions: Map[Identifier, Tree] = Map.empty

  protected def isTarget(x: Identifier): Boolean =
    targets.contains(x)

  protected def lookupTarget(x: Identifier): Tree =
    targets(x)

  protected def addTarget(x: Identifier, xTy: Tree): Unit = {
    assert(!targets.contains(x), s"Trying to target ${Printer.asString(x)} more than once")
    targets += x -> xTy
  }

  protected def removeTarget(x: Identifier): Unit = {
    assert(targets.contains(x))
    targets -= x
  }

  protected def interpreterContext(c: Context): Context =
    targets.toSeq.foldLeft(c) { case (acc, (x, ty)) =>
      solutions.get(x) match {
        case None => acc.bind(x, ty)
        case Some(t) => acc.bind(x, SingletonType(ty, t))
      }
    }

  protected def instantiateTarget(x: Identifier, tX: Tree): Unit = {
    if (solutions.contains(x))
      return
    // assert(!solutions.contains(x), s"${solutions.toSeq.map { case (k,v) => s"${Printer.asString(k)}: ${Printer.asString(v)}" } .mkString(", ")}")
    solutions = solutions.mapValues { tY => tY.replace(x, tX) } .toMap
    solutions += x -> tX
  }

  private def isSolving: Boolean =
    solverDepth > 0

  private def orRecover[A, B](tacA: Tactic[A,B], tacB: Tactic[A,B]): Tactic[A,B] =
    Tactic {
      case (g, subgoalSolver) =>
        // Checkpoint state and restore if first tactic fails
        val oldTargets = targets
        val oldSolutions = solutions
        val resultA = tacA.apply(g, subgoalSolver)
        resultA match {
          case result @ Some((true, _)) => result
          case _ =>
            // assert(targets.keySet == oldTargets.keySet) // TODO: Remove me
            targets = oldTargets // FIXME
            solutions = oldSolutions
            val resultB = tacB.apply(g, subgoalSolver)
            if (resultB.isDefined) resultB else resultA
        }
    }

  protected def solve(c: Context, x: Identifier, xTy: Tree, ty1: Tree, ty2: Tree): Option[Tree] = {
    addTarget(x, xTy)

    lazy val indent = " " * solverDepth
    if (rc.config.html) {
      rc.reporter.info(s"$indent┍ Solving for ${x.uniqueString} ...")
    }

    solverDepth += 1

    // NOTE: We first go through normalization.
    val g = NormalizedSubtypeGoal(c, ty1, ty2)
    val solveResult = tactic.apply(g, sg => None)

    // Even if we found some candidate, it doesn't validate the given subtyping query.
    val solveAttemptFailed = solveResult match {
      case None => true
      case Some((false, _)) => true
      case _ => false
    }

    solverDepth -= 1
    solveCount += 1

    if (rc.config.html) {
      solveResult match {
        case Some((success, tree)) =>
          val f = new java.io.File(s"./solve_${solveCount}_${x.uniqueString}")
          rc.reporter.info(s"$indent┕ Solver result: $success (${f.getAbsolutePath()})")
          util.HTMLOutput.makeHTMLFile(f, List(tree), success)
        case None =>
      }
    }

    val optSolution = solutions.get(x)
    // TODO: Also garbage-collect other, indirectly added targets and solutions?
    removeTarget(x)
    solutions = solutions - x

    if (solveAttemptFailed) {
      None
    } else {
      // TODO: Check whether solution is expressible in context `c`
      val solution = optSolution.getOrElse({
        // x was unconstrained, just pick some valid element
        rc.reporter.info(s"$indent  (Picked default solution for ${x.uniqueString}!)")
        xTy match {
          case TopType => LNil()
          case `LList` => LNil()
          case _ => ???
        }
      })

      Some(solution)
    }
  }

  // Search primitives

  // TODO: ...

  // Solving primitives

  protected def areEqualTrees(t1: Tree, t2: Tree): Boolean =
    if (isSolving) unify(t1, t2) else Tree.areEqual(t1, t2)

  private def unify(t1: Tree, t2: Tree): Boolean = {
    (t1, t2) match {
      case (IfThenElse(cond1, t11, t12), IfThenElse(cond2, t21, t22)) =>
        unify(cond1, cond2) && unify(t11, t21) && unify(t12, t22)
      case (App(t11, t12), App(t21, t22)) => unify(t11, t21) && unify(t12, t22)
      case (Succ(t1), Succ(t2)) => unify(t1, t2)
      case (Pair(t11, t12), Pair(t21, t22)) => unify(t11, t21) && unify(t12, t22)
      case (First(t1), First(t2)) => unify(t1, t2)
      case (Second(t1), Second(t2)) => unify(t1, t2)
      case (LeftTree(t1), LeftTree(t2)) => unify(t1, t2)
      case (RightTree(t1), RightTree(t2)) => unify(t1, t2)
      case (Because(t11, t12), Because(t21, t22)) => unify(t11, t21) && unify(t12, t22)
      case (Bind(x1, t1), Bind(x2, t2)) => unify(t1, t2.replace(x2, Var(x1)))
      case (Lambda(None, bind1), Lambda(None, bind2)) => unify(bind1, bind2)
      case (Lambda(Some(tp1), bind1), Lambda(Some(tp2), bind2)) => unify(tp1, tp2) && unify(bind1, bind2)
      case (ErasableLambda(tp1, bind1), ErasableLambda(tp2, bind2)) => unify(tp1, tp2) && unify(bind1, bind2)
      case (Fix(_, bind1), Fix(_, bind2)) => unify(bind1, bind2)
      case (LetIn(_, v1, bind1), LetIn(_, v2, bind2)) => unify(v1, v2) && unify(bind1, bind2)
      case (MacroTypeDecl(tpe1, bind1), MacroTypeDecl(tpe2, bind2)) => unify(tpe1, tpe2) && unify(bind1, bind2)
      case (MacroTypeInst(v1, args1), MacroTypeInst(v2, args2)) =>
        if (unify(v1, v2) && args1.size == args2.size)
          args1.zip(args2).forall { case (p1, p2) =>
            p1._1 == p2._1 &&
            unify(p1._2, p2._2)
          }
        else
          false
      case (NatMatch(n1, t1, bind1), NatMatch(n2, t2, bind2)) => unify(n1, n2) && unify(t1, t2) && unify(bind1, bind2)
      case (EitherMatch(t1, bind11, bind12), EitherMatch(t2, bind21, bind22)) =>
        unify(t1, t2) && unify(bind11, bind21) && unify(bind12, bind22)
      case (Primitive(op1, args1), Primitive(op2, args2)) =>
        if (op1 == op2 && args1.size == args2.size) args1.zip(args2).forall { case (t1, t2) => unify(t1, t2)}
        else false
      case (ErasableApp(t11, t12), ErasableApp(t21, t22)) => unify(t11, t21) && unify(t12, t22)
      case (Fold(tp1, t1), Fold(tp2, t2)) => unify(tp1, tp2) && unify(t1, t2)
      case (Unfold(t1, bind1), Unfold(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (UnfoldPositive(t1, bind1), UnfoldPositive(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (Abs(bind1), Abs(bind2)) => unify(bind1, bind2)
      case (TypeApp(abs1, t1), TypeApp(abs2, t2)) => unify(abs1, abs2) && unify(t1, t2)
      case (SumType(t1, bind1), SumType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (PiType(t1, bind1), PiType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (SigmaType(t1, bind1), SigmaType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (IntersectionType(t1, bind1), IntersectionType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (ExistsType(t1, bind1), ExistsType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (RefinementType(t1, bind1), RefinementType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (RefinementByType(t1, bind1), RefinementByType(t2, bind2)) =>
        // unify(t1, t2) &&  // FIXME: Why?
        unify(bind1, bind2)
      case (EqualityType(t11, t12), EqualityType(t21, t22)) => unify(t11, t21) && unify(t12, t22)
      case (RecType(t1, bind1), RecType(t2, bind2)) => unify(t1, t2) && unify(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => unify(bind1, bind2)
      case (Node(name1, args1), Node(name2, args2)) => name1 == name2 &&
        args1.zip(args2).forall { case (arg1, arg2) => unify(arg1, arg2) }
      case (Ascribe(t1, _), t2) => unify(t1, t2)
      case (t1, Ascribe(t2, _)) => unify(t1, t2)
      case (Var(x), Var(y)) if x == y => true
      case (Var(x), _) if isTarget(x) => instantiateTarget(x, t2); true
      case (_, Var(x)) if isTarget(x) => instantiateTarget(x, t1); true
      case _ => t1 == t2
    }
  }
}
