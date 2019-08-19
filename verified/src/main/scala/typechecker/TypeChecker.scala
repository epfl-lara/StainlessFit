package typechecker

import _root_.trees._
import _root_.solver._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import z3.scala._

import Derivation._

case class Context(
  val variables: List[Identifier],
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Identifier],
  val termEqualities: List[(Tree, Tree)],
  val level: Int,
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
) {
  def bind(i: Identifier, t: Tree) = {
    if (variables.contains(i)) throw new java.lang.Exception(s"Already bound ${i}")
    copy(
      termVariables = termVariables.updated(i, t),
      variables = i::variables
    )
  }

  def addTypeVariable(i: Identifier) = copy(typeVariables = typeVariables + i)

  def bindFresh(s: String, t: Tree) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree) = copy(termEqualities = (t1, t2)::termEqualities)

  def incrementLevel() = copy(level = level + 1)

  def containsVarOfType(tp: Tree): Boolean = variables.exists(termVariables(_) == tp)

  def getVarOfType(tp: Tree): Option[Identifier] = variables.find(termVariables(_) == tp)

  override def toString: String = {
    "Term equalities:\n" ++
    termEqualities.foldLeft("") {
      case (acc, (a, b)) => acc + s"${a} = ${b}\n"
    } ++ "Term variables:\n" ++
    variables.foldLeft("") {
      case (acc, id) => acc + s"${id}: ${termVariables(id)}\n"
    }
  }

  def hasSubstitution: Boolean = {
    termEqualities.exists {
      case (Var(x), t) => !x.isFreeIn(t)
      case (_, _) => false
    }
  }

  def hasRefinementBound: Boolean = {
    variables.exists { case v =>
      termVariables(v) match {
        case RefinementType(_, _) => true
        case _ => false
      }
    }
  }

  def hasValueSimplification: Boolean = {
    termEqualities.exists {
      case (t1, t2) => t1.hasValueSimplification || t2.hasValueSimplification
    }
  }

  def applyValueSimplification: Context = {
    copy(
      termEqualities = termEqualities.map { case (t1, t2) =>
        (t1.applyValueSimplification, t2.applyValueSimplification)
      }
    )
  }

  def typableIn(t: Tree): Boolean = {
    TypeChecker.inferInContext(this, t) match {
      case Some((s, _)) => s
      case _ => false
    }
  }

  def treeHasTopLevelSimplification(t: Tree): Boolean = {
    t match {
      case App(Lambda(_, _), t2) => typableIn(t2)
      case LetIn(_, t1, t2) => typableIn(t1)
      case EitherMatch(LeftTree(t), _, _) => typableIn(t)
      case EitherMatch(RightTree(t), _, _) => typableIn(t)
      case Unfold(Fold(_, t1), _) => typableIn(t1)
      case UnfoldPositive(Fold(_, t1), _) => typableIn(t1)
      case Primitive(op, l) => l.exists { case arg => treeHasTopLevelSimplification(arg) }
      case _ => false
    }
  }

  def hasTopLevelSimplification: Boolean = {
    termEqualities.exists {
      case (t1, t2) => treeHasTopLevelSimplification(t1) || treeHasTopLevelSimplification(t2)
    }
  }

  def treeApplyTopLevelSimplification(t: Tree): Tree = {
    t match {
      case App(Lambda(_, bind), t2) if typableIn(t2) && bind.isBind => Tree.replaceBind(bind, t2)
      case LetIn(_, t1, bind) if typableIn(t1) && bind.isBind => Tree.replaceBind(bind, t1)
      case EitherMatch(LeftTree(t), bind, _) if typableIn(t) && bind.isBind => Tree.replaceBind(bind, t)
      case EitherMatch(RightTree(t), _, bind) if typableIn(t) && bind.isBind => Tree.replaceBind(bind, t)
      case Unfold(Fold(_, t1), bind) if typableIn(t1) && bind.isBind => Tree.replaceBind(bind, t1)
      case UnfoldPositive(Fold(_, t1), bind) if typableIn(t1) && bind.isBind => Tree.replaceBind(bind, t1)
      case Primitive(op, l) if l.exists { case arg => treeHasTopLevelSimplification(arg) } =>
        Primitive(op, l.map { case arg => treeApplyTopLevelSimplification(arg) })

      case _ => t
    }
  }

  def applyTopLevelSimplification: Context = {
    copy(
      termEqualities = termEqualities.map { case (t1, t2) => (treeApplyTopLevelSimplification(t1), treeApplyTopLevelSimplification(t2))
      }
    )
  }


  def replace(id: Identifier, t: Tree): Context = {
    copy(
      termEqualities = termEqualities.map { case (t1, t2) => (Tree.replace(id, t, t1), Tree.replace(id, t, t2)) },
      termVariables = variables.foldLeft(Map[Identifier, Tree]()) { case (m, termId) => m.updated(termId, Tree.replace(id, t, termVariables(termId))) }
    )
  }

  def removeEquality(t1: Tree, t2: Tree): Context = {
    copy(termEqualities = termEqualities.filterNot { _ == (t1, t2) } )
  }
}


sealed abstract class Goal {
  val c: Context

  def removeEquality(t1: Tree, t2: Tree): Goal
  def replace(id: Identifier, t: Tree): Goal
  def hasValueSimplification: Boolean
  def applyValueSimplification: Goal
  def hasTopLevelSimplification: Boolean
  def applyTopLevelSimplification: Goal
}

case class InferGoal(c: Context, t: Tree) extends Goal {
  override def toString: String = {
    s"Inferring $t"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    InferGoal(c.replace(id, t1), t.replace(id, t1))
  }

  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification || t.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
      t = t.applyValueSimplification
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification || c.treeHasTopLevelSimplification(t)

  def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification,
      t = c.treeApplyTopLevelSimplification(t)
    )
  }
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${t}: ${tp}"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    CheckGoal(c.replace(id, t1), t.replace(id, t1), tp.replace(id, t1))
  }

  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification || t.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
      t = t.applyValueSimplification,
      tp = tp
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification || c.treeHasTopLevelSimplification(t)

  def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification,
      t = c.treeApplyTopLevelSimplification(t),
      tp = tp
    )
  }
}

case class SynthesizeGoal(c: Context, tp: Tree) extends Goal {
  def replace(id: Identifier, t: Tree): Goal = {
    SynthesizeGoal(c.replace(id, t), tp.replace(id, t))
  }

  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
      tp = tp
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification

  def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification,
      tp = tp
    )
  }
}

case class EqualityGoal(c: Context, t1: Tree, t2: Tree) extends Goal {
  override def toString: String = {
    s"Check equality ${t1} = ${t2}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EqualityGoal(c.replace(id, t), t1.replace(id, t), t2.replace(id, t))
  }

  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification || t1.hasValueSimplification || t2.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
      t1 = t1.applyValueSimplification,
      t2 = t2.applyValueSimplification
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification || c.treeHasTopLevelSimplification(t1) || c.treeHasTopLevelSimplification(t2)

  def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification,
      t1 = c.treeApplyTopLevelSimplification(t1),
      t2 = c.treeApplyTopLevelSimplification(t2)
    )
  }
}

case class ErrorGoal(c: Context, s: String) extends Goal {
  val level = 0

  override def toString: String = {
    s"Error Goal : ${s}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    ErrorGoal(c.replace(id, t), s)
  }

  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification

   def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification
    )
  }
}

case class EmptyGoal(c: Context) extends Goal {
  def removeEquality(t1: Tree, t2: Tree): Goal = copy(c = c.removeEquality(t1, t2))

  def hasValueSimplification: Boolean = c.hasValueSimplification

  def applyValueSimplification: Goal = {
    copy(
      c = c.applyValueSimplification,
    )
  }

  def hasTopLevelSimplification: Boolean = c.hasTopLevelSimplification

  def applyTopLevelSimplification: Goal = {
    copy(
      c = c.applyTopLevelSimplification
    )
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EmptyGoal(c.replace(id, t))
  }
}

object TypeOperators {
  private def unify(t1: Tree, t2: Tree, f: (Tree, Tree) => Tree): Option[Tree] = {
    (t1, t2) match {
      case (UnitType, UnitType) => Some(UnitType)
      case (NatType, NatType) => Some(NatType)
      case (BoolType, BoolType) => Some(BoolType)
      case (TopType, TopType) => Some(TopType)
      case (SumType(t11, t12), SumType(t21, t22)) =>
        unify(t11, t21, f).flatMap { t1 =>
          unify(t12, t22, f).map { t2 =>
            SumType(t1, t2)
          }
        }
      case (PiType(a1, Bind(x, b1)), PiType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            PiType(a, Bind(x, b))
          }
        }
      case (IntersectionType(a1, Bind(x, b1)), IntersectionType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            IntersectionType(a, Bind(x, b))
          }
        }
      case (PolyForallType(Bind(x, b1)), PolyForallType(Bind(x2, b2))) =>
        unify(b1, Tree.replace(x2, Var(x), b2), f).map(b =>
          PolyForallType(Bind(x, b))
        )
      case (SigmaType(a1, Bind(x, b1)), SigmaType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            SigmaType(a, Bind(x, b))
          }
        }
      case (RefinementType(a1, Bind(x, p1)), RefinementType(a2, Bind(x2, p2))) =>
        unify(a1, a2, f).map { a =>
          RefinementType(a, Bind(x, f(p1, Tree.replace(x2, Var(x), p2))))
        }
      case (RefinementType(a1, Bind(x, p1)), t3) =>
        unify(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (t3, RefinementType(a1, Bind(x, p1))) =>
        unify(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (RecType(n, Bind(x1, b1)), RecType(m, Bind(x2, b2))) =>
        unify(b1, Tree.replace(x2, Var(x1), b2), f).map { b =>
          RecType(f(n, m), Bind(x1, b))
        }
      case (EqualityType(t11, t12), EqualityType(t21, t22)) =>
        Some(EqualityType(f(t11, t21), f(t12, t22)))
      case (t1, t2) if t1 == t2 => Some(t1)
      case (_, _) => None()
    }
  }

  def ifThenElse(tc: Tree, t1: Tree, t2: Tree): Option[Tree] = {
    if (t1 == t2) Some(t1)
    else unify(t1, t2, (ty1: Tree, ty2: Tree) => IfThenElse(tc, ty1, ty2))
  }

  def matchSimpl(n: Tree, t0: Tree, id: Identifier, tn: Tree): Option[Tree] = {
    unify(t0, tn, (ty0: Tree, tyn: Tree) => Match(n, ty0, Bind(id, tyn)))
  }

  def eitherMatch(n: Tree, idl: Identifier, tl: Tree, idr: Identifier, tr: Tree): Option[Tree] = {
    unify(tl, tr, (tyl: Tree, tyr: Tree) => EitherMatch(n, Bind(idl, tyl), Bind(idr, tyr)))
  }

  def letIn(x: Identifier, tp: Option[Tree], v: Tree, t: Tree) = {
    def f(t1: Tree, t2: Tree): Tree = {
      if (x.isFreeIn(t1)) LetIn(tp, v, Bind(x, t1))
      else t1
    }
    unify(t, t, f)
  }

  def basetype(a: Identifier, t: Tree): Tree = {
    t match {
      case SigmaType(ty1, Bind(x, ty2)) =>
        SigmaType(basetype(a, ty1), Bind(x, basetype(a, ty2)))
      case SumType(ty1, ty2) =>
        SumType(basetype(a, ty1), basetype(a, ty2))
      case ty if a.isFreeIn(ty) => TopType
      case ty => ty
    }
  }

  def spos(a: Identifier, t: Tree): Boolean = {
    t match {
      case NatType => true
      case BoolType => true
      case BottomType => true
      case TopType => true
      case UnitType => true
      case Var(x) if x == a => true
      case t if !a.isFreeIn(t) => true
      case RefinementType(t, _) => spos(a, t)
      case PiType(t1, Bind(x, t2)) => !a.isFreeIn(t1) && spos(a, t2)
      case IntersectionType(t1, Bind(x, t2)) => !a.isFreeIn(t1) && spos(a, t2)
      case PolyForallType(Bind(x, t)) => spos(a, t)
      case SumType(t1, t2) => spos(a, t1) && spos(a, t2)
      case SigmaType(t1, Bind(_, t2)) => spos(a, t1) && spos(a, t2)
      case RecType(_, Bind(x, t)) =>
        spos(a, t) && (!a.isFreeIn(t) || spos(x, t))
      case _ => false
    }
  }
}

case class Tactic[T](apply: (Goal, (Goal => Option[T])) => Option[T]) {
  def ||(other: Tactic[T]): Tactic[T] = this.or(other)
  def or(other: Tactic[T]): Tactic[T] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, subgoalSolver) match {
          case None() => other.apply(g, subgoalSolver)
          case x => x
        }
    }

  def andThen(other: Tactic[T]): Tactic[T] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, sg => other.apply(sg, subgoalSolver))
    }

  def repeat: Tactic[T] = {
    def repeatApply(g: Goal, subgoalSolver: Goal => Option[T]): Option[T] = {
      apply(g, sg => repeatApply(sg, subgoalSolver))
    }
    Tactic[T](repeatApply)
  }
}

case class Rule(
  apply: Goal => Option[(
    List[List[Judgment] => Goal],
    List[Judgment] => (Boolean, Judgment))
  ]) {
  def t: Tactic[(Boolean, NodeTree[Judgment])] = Tactic { (g, subgoalSolver) =>
    apply(g).flatMap {
      case (sgs, merge) =>
        val subTrees: Option[(Boolean, List[NodeTree[Judgment]])] =
          sgs.foldLeft[Option[(Boolean, List[NodeTree[Judgment]])]](Some(true, List())) {
            case (accOpt, fsg) =>
              fsg match {
                case _: EmptyGoal =>
                  println("EmptyGoal")
                  accOpt
                case _ =>
                  accOpt.flatMap {
                    case (success, acc) =>
                      subgoalSolver(fsg(acc.map(_.node))).map { case (subSuccess: Boolean, subTree: NodeTree[Judgment]) =>
                        (success /*&& subSuccess*/, acc :+ subTree)
                      }
                  }
              }
          }
        subTrees.map { case (success, l) =>
          val (mergeSuccess, mergeJudgment) = merge(l.map(_.node))
          (success && mergeSuccess, NodeTree(mergeJudgment, l))
        }
    }
  }
}

object Rule {

  private def termOutput(t: Tree): String =
    Derivation.termColor(Derivation.shortString(t.toString))

  private def typeOutput(t: Tree): String =
    Derivation.typeColor(Derivation.shortString(t.toString))

  private def bold(s: String): String = Derivation.bold(s)

  val InferBool = Rule {
    case g @ InferGoal(c, BoolLiteral(b)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferBool : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((
        List(),
        _ => (true, InferJudgment(c, BoolLiteral(b), Some(BoolType)))
      ))
    case g =>
      None()
  }

  val InferNat = Rule {
    case g @ InferGoal(c, NatLiteral(n)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferNat : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment(c, NatLiteral(n), Some(NatType)))))
    case g =>
      None()
  }

  val InferUnit = Rule {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnit : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment(c, UnitLiteral, Some(UnitType)))))
    case g =>
      None()
  }

  val InferVar = Rule {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferVar : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None() => (false, ErrorJudgment(c, s"$id is not in context"))
          case Some(tpe) => (true, InferJudgment(c, Var(id), Some(tpe)))
        }
      ))

    case g =>
      None()
  }

  val CheckVar = Rule {
    case g @ CheckGoal(c, Var(id), ty) if c.termVariables.getOrElse(id, UnitLiteral).isEqual(ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckVar : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment(c, Var(id), ty))))
    case g =>
      None()
  }

  val InferError = Rule {
    case g @ InferGoal(c, e @ ErrorTree(_, Some(tp))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferError : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val errorGoal = EqualityGoal(c.incrementLevel(), BoolLiteral(false), BoolLiteral(true))
      Some((List(_ => errorGoal),
        {
          case Cons(AreEqualJudgment(_, _, _, _), _) => (true, InferJudgment(c, e, Some(tp)))
          case _ => (false, ErrorJudgment(c, s"Could not infer ${typeOutput(tp)} for ${termOutput(e)} with InferError."))
        }
      ))

    case g =>
      None()
  }

  val InferLet = Rule {
    case g @ InferGoal(c, e @ LetIn(None(), v, Bind(id, body))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, Some(tyv)), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c, s"Could not infer type for ${termOutput(v)}, then body of let is not typechecked.")
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(InferJudgment(_, _, Some(tyb)), _)) =>
            (true, InferJudgment(c, e, Some(tyb)))
          case _ =>
            (false, ErrorJudgment(c, InferJudgment(c, e, None())))
        }
      ))

    case g @ InferGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _), Cons(InferJudgment(_, _, Some(tyb)), _)) =>
            (true, InferJudgment(c, e, Some(tyb)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferLet."))
        }
      ))

    case g =>
      None()
  }

  val InferLambda = Rule {
    case g @ InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case Cons(InferJudgment(_, _, Some(tyb)), _) =>
            (true, InferJudgment(c, e, Some(PiType(ty1, Bind(id, tyb)))))
          case _ =>
            (true, InferJudgment(c, e, Some(TopType)))
            //(false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferLambda."))
        }
      ))

    case g =>
      None()
  }

  val InferIf = Rule {
    case g @ InferGoal(c, e @ IfThenElse(tc, t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BoolLiteral(true))
      val c2 = c0.addEquality(tc, BoolLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val inferT1 = InferGoal(c1, t1)
      val inferT2 = InferGoal(c2, t2)
      val checkContext1 = EqualityGoal(c1, BoolLiteral(true), BoolLiteral(false))
       val checkContext2 = EqualityGoal(c2, BoolLiteral(true), BoolLiteral(false))
      Some((
        List(_ => checkCond, _ => inferT1, _ => inferT2, _ => checkContext1, _ => checkContext2),
        {
          case Cons(CheckJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(InferJudgment(_, _, Some(ty2)),
            _
          ))) =>
            TypeOperators.ifThenElse(tc, ty1, ty2) match {
              case None() => (false,
                ErrorJudgment(
                  c,
                  s"Could not infer type for ${termOutput(e)} with InferIf: cannot unify ${typeOutput(ty1)}  and ${typeOutput(ty2)}"
                )
              )
              case Some(ty) =>
                (true, InferJudgment(c, e, Some(ty)))
            }

          case _ =>
            (false, ErrorJudgment(c, s"COuld not infer type for ${termOutput(e)} with InferIf."))
        }
      ))

    case g =>
      None()
  }

  val InferBinaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Cons(n2, Nil())))) if op.isBinOp =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferBinaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel, n1, opType)
      val checkN2 = CheckGoal(c.incrementLevel, n2, opType)
      val checkEq = EqualityGoal(c.incrementLevel, Primitive(Gteq, List(n1, n2)), BoolLiteral(true))
      Some((
        if(op == Minus) List(_ => checkN1, _ => checkN2, _ => checkEq) else List(_ => checkN1, _ => checkN2),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _, _), _))) =>
            (true, InferJudgment(c, e, Some(NatType)))
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) if op != Minus =>
            (true, InferJudgment(c, e, Some(op.returnedType)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferBinaryPrimitive."))
        }
      ))

    case _ => None()
  }

  val InferUnaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Nil()))) if op.isUnOp =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel, n1, opType)
      Some((
        List(_ => checkN1),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, InferJudgment(c, e, Some(op.returnedType)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnaryPrimitive."))
        }
      ))

    case _ => None()
  }

  val InferMatch = Rule {
    case g @ InferGoal(c, e @ Match(t, t0, Bind(id, tn))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferMatch: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val inferT0 = InferGoal(c0, t0)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val inferTn = InferGoal(cn, tn)
      Some((
        List(_ => checkN, _ => inferT0, _ => inferTn), {
          case Cons(CheckJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty0)),
            Cons(InferJudgment(_, _, Some(tyn)), _
          ))) =>
            TypeOperators.matchSimpl(t, ty0, id, tyn) match {
              case None() => (false,
                ErrorJudgment(
                  c,
                  s"Could not infer type for ${termOutput(e)} with InferMatch: cannot unify types ${typeOutput(ty0)} and ${typeOutput(tyn)}."
                )
              )
              case Some(ty) => (true, InferJudgment(c, e, Some(ty)))
            }

          case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferMatch."))
        }
      ))

    case _ => None()
  }

  val InferEitherMatch = Rule {
    case g @ InferGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val finferT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)}, then body of either_match is not typechecked.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}, then body of either_match is not typechecked.")
      }
      val finferT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)} then body of either_match is not typechecked.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)} then body of either_match is not typechecked.")
      }

      val checkContext1: List[Judgment] => Goal = {
        case Cons(_, Cons(InferJudgment(c1, _, Some(ty1)),
             Cons(InferJudgment(_, _, Some(ty2)), _))) =>
          TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
            case None() => EqualityGoal(c1, BoolLiteral(true), BoolLiteral(false))
            case Some(ty) => EmptyGoal(c)
          }
        case Cons(_, Cons(ErrorJudgment(c1, _),
             Cons(InferJudgment(_, _, Some(ty2)), _))) => EqualityGoal(c1, BoolLiteral(true), BoolLiteral(false))
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}, then body of either_match is not typechecked.")
      }

      val checkContext2: List[Judgment] => Goal = {
        case Cons(_, Cons(InferJudgment(_, _, Some(ty1)),
             Cons(InferJudgment(c2, _, Some(ty2)), _))) =>
          TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
            case None() => EqualityGoal(c2, BoolLiteral(true), BoolLiteral(false))
            case Some(ty) => EmptyGoal(c)
          }
        case Cons(_, Cons(InferJudgment(_, _, Some(ty1)),
             Cons(ErrorJudgment(c2, _), _))) => EqualityGoal(c2, BoolLiteral(true), BoolLiteral(false))
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}, then body of either_match is not typechecked.")
      }

      Some((
        List(_ => inferScrutinee, finferT1, finferT2, checkContext1, checkContext2), {
          case Cons(InferJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(InferJudgment(_, _, Some(ty2)),
            Cons(EmptyJudgment(_),
            Cons(EmptyJudgment(_), _))))) => (true, InferJudgment(c, e, Some(TypeOperators.eitherMatch(t, id1, ty1, id2, ty2).get)))

          case Cons(InferJudgment(_, _, _),
            Cons(_,
            Cons(InferJudgment(_, _, Some(ty2)),
            Cons(AreEqualJudgment(_, _, _, _), _)))) => (true, InferJudgment(c, e, Some(ty2)))

          case Cons(InferJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(_,
            Cons(_,
            Cons(AreEqualJudgment(_, _, _, _), _))))) => (true, InferJudgment(c, e, Some(ty1)))

          case _ => (false, ErrorJudgment(c, s"Could not infer a type for ${termOutput(e)} with InferEitherMatch."))
        }
      ))

    case _ => None()
  }

  val InferFix = Rule {
    case g @ InferGoal(c, e @ Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFix : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      // If n1 != n, fail
      val m = Identifier(0, "_M")
      val c1 = c.incrementLevel().bind(n, NatType).bind(
        y,
        PiType(UnitType, Bind(Identifier(0, "_"),
          IntersectionType(
            RefinementType(NatType, Bind(m, Primitive(Lt, List(Var(m), Var(n))))),
            Bind(m, Tree.replace(n, Var(m), ty))))
        )
      ).addEquality(
        Var(y),
        Lambda(
          Some(UnitType),
          Bind(Identifier(0, "_Unit"), Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))))
      )
      Some((
        List(_ => CheckGoal(c1, t, ty)), {
          case Cons(CheckJudgment(_, _, _), _) =>
            if(n.isFreeIn(t.erase))
              (false, ErrorJudgment(c, s"Could not infer a type for ${termOutput(e)} with InferFix: ${termOutput(Var(n))} appears free in ${termOutput(t.erase)}."))
            else
             (true, InferJudgment(c, e, Some(IntersectionType(NatType, Bind(n, ty)))))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer a type for ${termOutput(e)} with InferFix."))
        }
      ))

    case _ => None()
  }

  val InferFixFail = Rule {
    case g @ InferGoal(c, e @ Fix(None(), Bind(n1, Bind(y, t)))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFixFail : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (false, ErrorJudgment(c, s"Could not infer a type for fix without annotation ${termOutput(e)}"))))

    case _ => None()
  }

  val InferForallInstantiation = Rule {
    case g @ InferGoal(c, e @ Inst(t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferForallInstantiation : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case IntersectionType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting an intersection type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, Some(ty)),
            Cons(CheckJudgment(_, _, _), _)) =>

            dropRefinements(ty) match {
              case IntersectionType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() =>
                    (false, ErrorJudgment(c,
                    s"Could not infer type for ${termOutput(e)} with InferIntersectionInstantiation: error in letIn($x, ${termOutput(t2)}, ${typeOutput(ty)})."))
                  case Some(t) =>
                    (true, InferJudgment(c, e, Some(t)))
                }
              case _ => (false, ErrorJudgment(c,
              s"Could not infer type for ${termOutput(e)} with InferIntersectionInstantiation: expecting an intersection type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }

          case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferIntersectionInstantiation."))
        }
      ))

    case _ => None()
  }

  val InferApp = Rule {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferApp : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting a pi type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, Some(ty)),
            Cons(CheckJudgment(_, _, _), _)) =>
            dropRefinements(ty) match {
              case PiType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferApp: error in letIn($x, ${termOutput(t2)}, ${typeOutput(ty)})."))
                  case Some(t) =>
                    (true, InferJudgment(c, e, Some(t)))
                }
              case _ => (false, ErrorJudgment(c,
                s"Could not infer type for ${termOutput(e)} with InferApp: expecting a pi type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }

          case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferApp."))
        }
      ))

    case _ => None()
  }

  val UnsafeIgnoreEquality = Rule {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug(s"Context:\n${c}\n")
      TypeChecker.equalityDebug(s"Ignoring equality ${t1} = ${t2}.\n\n")
      Some(List(), _ => (false, ErrorJudgment(c, s"Equality between ${termOutput(t1)} and ${termOutput(t2)} ${bold("IGNORED")}.")))
    case g =>
      None()
  }

  val CatchErrorGoal = Rule {
    case ErrorGoal(c, s) =>
      Some(List(), _ => (false, ErrorJudgment(c, s)))
    case g =>
      None()
  }

  val CatchEmptyGoal = Rule {
    case EmptyGoal(c) =>
      Some(List(), _ => (true, EmptyJudgment(c)))
    case g =>
      None()
  }

  def dropRefinements(t: Tree): Tree = {
    t match {
      case RefinementType(ty, _) => dropRefinements(ty)
      case _ => t
    }
  }

  val CheckRefinement = Rule {
    case g @ CheckGoal(c, t, tpe @ RefinementType(ty, Bind(id, b))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRefinement : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val checkTy = CheckGoal(c.incrementLevel, t, ty)
      val c1 = c.bind(id, ty).addEquality(Var(id), t)
      val checkRef = EqualityGoal(c1.incrementLevel, b, BoolLiteral(true))
      Some((
        List(_ => checkTy, _ => checkRef), {
          case Cons(CheckJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckRefinement."))
        }
      ))

    case _ => None()
  }

  val CheckReflexive = Rule {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckReflexive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gInfer = InferGoal(c.incrementLevel(), t)
      Some((List(_ => gInfer),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) if (dropRefinements(tpe) == ty) =>
            (true, CheckJudgment(c, t, ty))
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(ty)} with CheckReflexive: infer ${typeOutput(tpe)}."))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(ty)} with CheckReflexive: no type infer."))
        }
      ))
    case g =>
      None()
  }

  val FailRule = Rule {
    case InferGoal(c, e) =>
      throw new java.lang.Exception(s"Inference failed for term (${e.getClass}):\n$e")
    case g =>
      throw new java.lang.Exception(s"Goal is not handled:\n$g")
  }

  val InferPair = Rule {
    case g @ InferGoal(c, e @ Pair(t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferPair : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val inferFirst = InferGoal(c.incrementLevel, t1)
        val inferSecond = InferGoal(c.incrementLevel, t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case Cons(InferJudgment(_, _, Some(ty1)), Cons(InferJudgment(_, _, Some(ty2)), _)) =>
            val inferedType = SigmaType(ty1, Bind(Identifier(0, "X"), ty2))
            (true, InferJudgment(c, e, Some(inferedType)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferPair."))
        }
      ))
    case g =>
      None()
  }

  val InferFirst = Rule {
    case g @ InferGoal(c, e @ First(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFirst : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(SigmaType(ty, _))), _) =>
            (true, InferJudgment(c, e, Some(ty)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferFirst."))
        }
      ))
    case g =>
      None()
  }

  val InferSecond = Rule {
    case g @ InferGoal(c, e @ Second(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferSecond : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(SigmaType(_, Bind(x, ty)))), _) =>
            TypeOperators.letIn(x, None(), First(t), ty) match {
                  case None() => (false, ErrorJudgment(c,
                    s"Could not infer type for ${termOutput(e)} with InferSecond: error in letIn($x, ${termOutput(First(t))}, ${typeOutput(ty)})"))
                  case Some(t) => (true, InferJudgment(c, e, Some(t)))
                }
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferSecond."))
        }
      ))
    case g =>
      None()
  }

  val InferLeft = Rule {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (true, InferJudgment(c, e, Some(SumType(tpe, BottomType))))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferLeft."))
        }
      ))
    case g =>
      None()
  }

  val InferRight = Rule {
    case g @ InferGoal(c, e @ RightTree(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (true, InferJudgment(c, e, Some(SumType(BottomType, tpe))))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferRight."))
        }
      ))
    case g =>
      None()
  }

  val CheckLeft = Rule {
    case g @ CheckGoal(c, e @ LeftTree(t), tpe @ SumType(ty, _)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel, t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckLeft."))
        }
      ))
    case g =>
      None()
  }

  val CheckRight = Rule {
    case g @ CheckGoal(c, e @ RightTree(t), tpe @ SumType(_, ty)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel, t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckRight."))
        }
      ))
    case g =>
      None()
  }

  val CheckLambda = Rule {
    case g @ CheckGoal(c, e @ Lambda(Some(ty1), Bind(id1, body)), tpe @ PiType(ty2, Bind(id2, ty))) if (ty1.isEqual(ty2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id1.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel, body.replace(id1, Var(freshId)), ty.replace(id2, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckLambda."))
        }
      ))
    case g =>
      None()
  }

  val CheckPi = Rule {
    case g @ CheckGoal(c, e @ t, tpe @ PiType(ty1, Bind(id,ty2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckPi : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel, App(t, Var(freshId)), ty2.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckPi."))
        }
      ))
    case g =>
      None()
  }

  val CheckIf = Rule {
    case g @ CheckGoal(c, e @ IfThenElse(tc, t1, t2), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BoolLiteral(true))
      val c2 = c0.addEquality(tc, BoolLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val checkT1 = CheckGoal(c1, t1, ty)
      val checkT2 = CheckGoal(c2, t2, ty)
      Some((
        List(_ => checkCond, _ => checkT1, _ => checkT2),
        {
          case Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _),
            _
          ))) =>
            (true, CheckJudgment(c, e, ty))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckIf."))
        }
      ))

    case g =>
      None()
  }

  val CheckMatch = Rule {
    case g @ CheckGoal(c, e @ Match(t, t0, Bind(id, tn)), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckkMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val checkT0 = CheckGoal(c0, t0, ty)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val checkTn = CheckGoal(cn, tn, ty)
      Some((
        List(_ => checkN, _ => checkT0, _ => checkTn), {
          case Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _), _
          ))) =>
            (true, CheckJudgment(c, e, ty))
          case _ => (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckMatch."))
        }
      ))

    case _ => None()
  }

  val CheckEitherMatch = Rule {
    case g @ CheckGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), tpe) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val fcheckT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, tpe)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)}.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}.")
      }
      val fcheckT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              CheckGoal(c2, t2, tpe)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)}.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}.")
      }
      Some((
        List(_ => inferScrutinee, fcheckT1, fcheckT2), {
          case Cons(InferJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _), _
          ))) =>
            (true, CheckJudgment(c, e, tpe))

          case _ => (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckEitherMatch."))
        }
      ))

    case _ => None()
  }

  val CheckPair = Rule {
    case g @ CheckGoal(c, e @ Pair(t1, t2), ty @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckFirst : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal1 = CheckGoal(c.incrementLevel, t1, ty1)
      val subgoal2 = CheckGoal(c.incrementLevel, t2, TypeOperators.letIn(id, None(), t1, ty2).get)
      Some((List(_ => subgoal1, _ => subgoal2),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, e, ty))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckPair."))
        }
      ))
    case g =>
      None()
  }

  val CheckSigma = Rule {
    case g @ CheckGoal(c, t, tpe @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckSigma : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val checkFirst = CheckGoal(c.incrementLevel, First(t), ty1)
        val c1 = c.bind(id, ty2).addEquality(Var(id), First(t)).incrementLevel
        val checkSecond = CheckGoal(c1, Second(t), ty2)
      Some((List(_ => checkFirst, _ => checkSecond),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckSigma."))
        }
      ))
    case g =>
      None()
  }

  val CheckIntersection = Rule {
    case g @ CheckGoal(c, t, tpe @ IntersectionType(tyid, Bind(id, ty))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckIntersection : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id.name, tyid)
      val subgoal = CheckGoal(c1.incrementLevel, Inst(t, Var(freshId)), ty.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckIntersection."))
        }
      ))
    case g =>
      None()
  }

  val CheckLet = Rule {
    case g @ CheckGoal(c, e @ LetIn(None(), v, Bind(id, body)), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, Some(tyv)), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            CheckGoal(c1, body, ty)
          case _ =>
            ErrorGoal(c, s"Could not infer type for ${termOutput(v)}")
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(CheckJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, e, ty))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckLet."))
        }
      ))

    case g @ CheckGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body)), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = CheckGoal(c1, body, ty)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, e, ty))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckLet."))
        }
      ))

    case g =>
      None()
  }

  val InferFold = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ RecType(n, Bind(a, ty))), t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFold : ${g.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val checkN = CheckGoal(c.incrementLevel, n, NatType)
      val c1 = c.addEquality(n, NatLiteral(0))
      val checkBase = CheckGoal(c1.incrementLevel, t, TypeOperators.basetype(a, ty))
      val (id, c2) = c.bindFresh("_n", NatType)
      val n2 = Var(id)
      val c3 = c2.addEquality(
        n,
        Primitive(Plus, List(n2, NatLiteral(1)))
      )
      val nTy = RecType(n2, Bind(a, ty))
      val check = CheckGoal(c3.incrementLevel, t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => checkN, _ => checkBase, _ => check),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _))) =>
            (true, InferJudgment(c, e, Some(tpe)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferFold."))
        }
      ))
    case g =>
      None()
  }

  val InferFoldFail = Rule {
    case g @ InferGoal(c, e @ Fold(None(), t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFoldFail : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (false, ErrorJudgment(c, s"Could not infer a type for fold without annotation ${termOutput(e)}"))))

    case _ => None()
  }

  val CheckRecursive = Rule {
    case g @ CheckGoal(c, t, tpe @ RecType(n, Bind(a, ty))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRecursive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel, t)
      val fEquality: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, Some(ty)), _) =>
            dropRefinements(ty) match {
              case RecType(n2, Bind(b, ty2)) =>
                EqualityGoal(c.incrementLevel, n, n2)
              case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t)}, found ${typeOutput(ty)}.")
            }
          case _ =>
            ErrorGoal(c, s"Could not infer type for ${termOutput(t)}")
        }
      Some((
        List(_ => subgoal, fEquality),
        {
          case Cons(InferJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(t)} with CheckRec."))
        }
      ))

    case _ => None()
  }

 val CheckTop2 = Rule {
    case g @ CheckGoal(c, t, TopType) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTop2 : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, t, TopType))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(TopType)} with CheckTop2."))
        }
      ))
    case g =>
      None()
  }

  val CheckTop1 = Rule {
    case g @ CheckGoal(c, t, TopType) if t.isValue =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTop1 : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment(c, t, TopType))))
    case g =>
      None()
  }

  val InferUnfold = Rule {
    case g @ InferGoal(c, e @ Unfold(t1, Bind(x, t2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnfold : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case RecType(n, Bind(a, ty)) =>
              val c1 = c0.bind(x, TypeOperators.basetype(a, ty)).addEquality(
                t1,
                Fold(Some(RecType(NatLiteral(0), Bind(a, ty))), Var(x))
              ).addEquality(n, NatLiteral(0))
              InferGoal(c1, t2)
            case ty @ IntersectionType(NatType, Bind(n, RecType(m, Bind(a, tpe)))) =>
              val nTy = tpe.replace(a, ty)
              val c1 = c0.bind(x, nTy).addEquality(t1, Fold(Some(ty), Var(x)))
              InferGoal(c1, t2)
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      val fg3: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case RecType(n, Bind(a, ty)) =>
              val nTy = Tree.replace(a, RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty)), ty)
              val c2 = c.addEquality(
                t1,
                Fold(Some(RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty))), Var(x))
              ).bind(x, nTy)
              InferGoal(c2, t2)
            case ty @ IntersectionType(NatType, Bind(n, RecType(m, Bind(a, _)))) =>
              EmptyGoal(c0)
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
          ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg2, fg3), {
          case Cons(InferJudgment(_, _, Some(ty)),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(j3, _))) =>
            dropRefinements(ty) match {
              case IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty)))) =>
                if(TypeOperators.spos(a, ty)) (true, InferJudgment(c, e, Some(ty1)))
                else (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnFold: $a does not appears strictly positively in ${typeOutput(ty)}"))

              case RecType(n, Bind(x, ty)) =>
                j3 match {
                  case InferJudgment(_, _, Some(ty2)) =>
                    if(ty1.isEqual(ty2)) (true, InferJudgment(c, e, Some(ty1)))
                    else {
                      (
                        false,
                        ErrorJudgment(
                          c,
                          s"Could not infer type for ${termOutput(e)} with InferFold: ${typeOutput(ty1)} not equal to ${typeOutput(ty2)}."
                        )
                      )
                    }
                  case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferFold."))
                }
               case _ =>
                (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnFold: expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }
          case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnFold."))
        }
      ))

    case _ => None()
  }

  val NewInferUnfoldPositive = Rule {
    case g @ InferGoal(c, e @ UnfoldPositive(t1, Bind(x, t2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnfoldPositive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg3: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case RecType(n, Bind(a, ty)) =>
              val nTy = Tree.replace(a, RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty)), ty)
              val c2 = c.addEquality(
                t1,
                Fold(Some(RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty))), Var(x))
              ).bind(x, nTy)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
          ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg3), {
          case Cons(InferJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty2)), _)) =>
            (true, InferJudgment(c, e, Some(ty2)))
          case _ => (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnFold."))
        }
      ))

    case _ => None()
  }

  val InferTypeAbs = Rule {
    case g @ InferGoal(c, e @ Abs(Bind(a, t))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferTypeAbs : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (true, InferJudgment(c, e, Some(PolyForallType(Bind(a, tpe)))))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferTypeAbs."))
        }
      ))
    case g =>
      None()
  }

  val InferTypeApp = Rule {
    case g @ InferGoal(c, e @ TypeApp(t, Some(ty))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferTypeApp : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(PolyForallType(Bind(x, tpe)))), _) =>
            (true, InferJudgment(c, e, Some(tpe.replace(x, ty))))
          case Cons(InferJudgment(_, _, Some(ty)), _) =>
            (false, ErrorJudgment(c,
              s"Could not infer type for ${termOutput(e)} with InferTypeApp: expecting poly forall type for ${termOutput(t)}, found ${typeOutput(ty)}."))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferTypeApp."))
        }
      ))
    case g =>
      None()
  }

  val CheckTypeAbs = Rule {
    case g @ CheckGoal(c, t, tpe @ PolyForallType(Bind(a, ty))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTypeAbs : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = CheckGoal(c1, TypeApp(t, Some(Var(a))), ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckTypeAbs."))
        }
      ))
    case g =>
      None()
  }


  def useContextEqualities(g: Goal): Goal = {
    g.c.termEqualities.find {
      case (Var(id), t1) => !id.isFreeIn(t1)
      case _ => false
    } match {
      case Some((Var(id), t1)) =>
        useContextEqualities(g.removeEquality(Var(id), t1).replace(id, t1))
      case _ => g
    }
  }

  val NewUseContextEqualities = Rule {
    case g @ EqualityGoal(c, t1, t2) if c.hasSubstitution =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} UseContextEqualities : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val g1 = useContextEqualities(g)
      Some((List(_ => g1),
        {
          case Cons(AreEqualJudgment(_, _, _, b), _) =>
            (true, AreEqualJudgment(c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment(c,
            s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewUseContextEqualities."))
        }
      ))
    case g =>
      None()
  }

  def unfoldRefinementInContext(c: Context): Context = {
    val c1 = c.variables.foldLeft(c) { case (acc, x) =>
      c.getTypeOf(x) match {
        case Some(RefinementType(ty, Bind(y, t2))) =>
          val t2p = Tree.replace(y, Var(x), t2)
          c.copy(
            termVariables = c.termVariables.updated(x, ty),
            termEqualities = (t2p, BoolLiteral(true))::c.termEqualities
          )
        case _ => acc
      }
    }
    c1
  }

  val NewUnfoldRefinementInContext = Rule {
    case g @ EqualityGoal(c, t1, t2) if c.hasRefinementBound =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} UnfoldRefinementInContext : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = unfoldRefinementInContext(c)
      val subgoal = EqualityGoal(c1.incrementLevel, t1, t2)
      Some((List(_ => subgoal),
        {
          case Cons(AreEqualJudgment(_, _, _, b), _) =>
            (true, AreEqualJudgment(c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewUnfoldRefinementInContext."))
        }
      ))
    case g =>
      None()
  }

  val NewApplyValueSimplification = Rule {
    case g @ EqualityGoal(c, t1, t2) if g.hasValueSimplification =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} ApplyValueSimplification: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal =  g.applyValueSimplification
      Some((List(_ => subgoal),
        {
          case Cons(AreEqualJudgment(_, _, _, b), _) =>
            (true, AreEqualJudgment(c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewApplyValueSimplification."))
        }
      ))
    case g =>
      None()
  }

  val InferFoldGen = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty))))), t)) =>
      /* Fail if n != m */
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFoldGen : ${g.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val nTy = IntersectionType(NatType, Bind(n, RecType(Var(n), Bind(a, ty))))
      val check = CheckGoal(c.incrementLevel, t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => check),
        {
          case Cons(CheckJudgment(_, _, _), _) if TypeOperators.spos(a, ty) =>
            (true, InferJudgment(c, e, Some(tpe)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer type for ${termOutput(e)} with InferUnFoldGen."))
        }
      ))
    case g =>
      None()
  }


  val NewEqualityInContext = Rule {
    case g @ EqualityGoal(c, t1, t2) if c.termEqualities.contains((t1, t2)) || c.termEqualities.contains((t2, t1)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} EqualityInContext: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment(c, t1, t2, "By Assumption"))
        }
      ))
    case g =>
      None()
  }

  val NewContradiction = Rule {
    case g @ EqualityGoal(c, t1, t2) =>
      if (c.getVarOfType(BottomType).isEmpty) None()
      else {
        TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewContradiction: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val x = c.getVarOfType(BottomType).get
        Some((List(),
          {
            case _ => (true, AreEqualJudgment(c, t1, t2, s"By Contradiction (term in ${typeOutput(BottomType)})"))
          }
        ))
      }
    case g =>
      None()
  }


  val NewApplyTopLevelSimplification = Rule {
    case g @ EqualityGoal(c, t1, t2) if g.hasTopLevelSimplification =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewApplyTopLevelSimplification : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = g.applyTopLevelSimplification
      Some((List(_ => subgoal),
        {
          case Cons(AreEqualJudgment(_, _, _, b), _) =>
            (true, AreEqualJudgment(c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewApplyTopLevelSimplification."))
        }
      ))
    case g =>
      None()
  }


  def topIf(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case IfThenElse(tc, tt, tf) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, BoolLiteral(true))
        val c2 = c0.addEquality(tc, BoolLiteral(false))
        val checkC = CheckGoal(c0, tc, BoolType)
        val equalT1 = EqualityGoal(c1, tt, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => checkC, _ => equalT1, _ => equalT2),
          {
            case Cons(CheckJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _), _))) =>
              (true, AreEqualJudgment(c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewTopIf."))
          }
        ))
      case _ => None()
    }
  }

  val NewTopIf = Rule {
    case g @ EqualityGoal(c, t1 @ IfThenElse(tc, tt, tf), t2) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topIf(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ IfThenElse(tc, tt, tf)) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topIf(c, t2, t1)
    case g =>
      None()
  }


  def topMatch(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case Match(tc, t0, Bind(y, tf)) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, NatLiteral(0))
        val c2 = c0.addEquality(tc, Primitive(Plus, List(Var(y), NatLiteral(1)))).bind(y, NatType)
        val checkC = CheckGoal(c0, tc, NatType)
        val equalT1 = EqualityGoal(c1, t0, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => checkC, _ => equalT1, _ => equalT2),
          {
            case Cons(CheckJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _), _))) =>
              (true, AreEqualJudgment(c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewTopEitherMatch."))
          }
        ))
      case _ => None()
    }
  }

  val NewTopMatch = Rule {
    case g @ EqualityGoal(c, t1 @ Match(tc, tt, tf), t2) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopMath : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ Match(tc, tt, tf)) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t2, t1)
    case g =>
      None()
  }



  // TODODO : find a good way to check the type of tc, or maybe just infer it.
  def topEitherMatch(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case EitherMatch(tc, Bind(x, tt), Bind(y, tf)) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, LeftTree(Var(x)))
        val c2 = c0.addEquality(tc, RightTree(Var(y)))
        val equalT1 = EqualityGoal(c1, tt, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => equalT1, _ => equalT2),
          {
            case Cons(AreEqualJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _), _)) =>
              (true, AreEqualJudgment(c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)} with NewTopEitherMatch."))
          }
        ))
      case _ => None()
    }
  }

  val NewTopEitherMatch = Rule {
    case g @ EqualityGoal(c, t1 @ EitherMatch(tc, tt, tf), t2) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopEitherMath : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ EitherMatch(tc, tt, tf)) if c.typableIn(tc) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t2, t1)
    case g =>
      None()
  }


  def isNatExpression(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case Var(id) => termVariables.contains(id) && dropRefinements(termVariables(id)) == NatType
      case NatLiteral(_) => true
      case Primitive(op, Cons(n1, Cons(n2, Nil()))) =>
        op.isNatToNatBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)
      case _ => false
    }
  }

  def isNatPredicate(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case BoolLiteral(_) => true
      case Primitive(Eq, Cons(n1, Cons(n2, Nil()))) =>
        (isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
        (isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
      case Primitive(op, Cons(n1, Cons(n2, Nil()))) =>
        (op.isNatToBoolBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
        (op.isBoolToBoolBinOp && isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
      case Primitive(op, Cons(b, Nil())) => op.isBoolToBoolUnOp && isNatPredicate(termVariables, b)
      case _ => false
    }
  }

  var x: BigInt = 0

  def unique(): BigInt = {
    x = x + 1
    x
  }

  def z3Encode(z3: Z3Context, solver: Z3Solver, variables: Map[Identifier, Z3AST], t: Tree): Z3AST = {
    t match {
      case Var(id) => variables(id)
      case NatLiteral(n) => z3.mkInt(n.toInt, z3.mkIntSort())
      case BoolLiteral(true) => z3.mkTrue()
      case BoolLiteral(false) => z3.mkFalse()
      case Primitive(Eq, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkEq(n1AST, n2AST)
      case Primitive(Neq, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkNot(z3.mkEq(n1AST, n2AST))
      case Primitive(Lteq, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkLE(n1AST, n2AST)
      case Primitive(Gteq, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkGE(n1AST, n2AST)
      case Primitive(Lt, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkLT(n1AST, n2AST)
      case Primitive(Gt, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkGT(n1AST, n2AST)
      case Primitive(Minus, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkSub(n1AST, n2AST)
      case Primitive(Plus, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkAdd(n1AST, n2AST)

      case Primitive(Mul, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkMul(n1AST, n2AST)

      case Primitive(Div, Cons(n1, Cons(n2, Nil()))) =>
        val n1AST = z3Encode(z3, solver, variables, n1)
        val n2AST = z3Encode(z3, solver, variables, n2)
        z3.mkDiv(n1AST, n2AST)

      case Primitive(Not, Cons(b, Nil())) =>
        val bAST = z3Encode(z3, solver, variables, b)
        z3.mkNot(bAST)

      case Primitive(And, Cons(b1, Cons(b2, Nil()))) =>
        val b1AST = z3Encode(z3, solver, variables, b1)
        val b2AST = z3Encode(z3, solver, variables, b2)
        z3.mkAnd(b1AST, b2AST)

      case Primitive(Or, Cons(b1, Cons(b2, Nil()))) =>
        val b1AST = z3Encode(z3, solver, variables, b1)
        val b2AST = z3Encode(z3, solver, variables, b2)
        z3.mkOr(b1AST, b2AST)

      // case Primitive(op, Cons(n1, Cons(n2, Nil()))) => ()

      case _ => throw new java.lang.Exception(s"Error while making Z3 constraints. Unsupported tree: $t")
    }
  }

  val NewZ3ArithmeticSolver = Rule {
    case g @ EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, Cons(t1, Cons(t2, Nil())))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} Z3ArithmeticSolver: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val factory = Solver.getFactory
      val z3 = factory.getContext
      val solver = z3.mkSolver
      val i = z3.mkIntSort

      val z3Variables =
        ListOps.toMap(c.variables.filter(c.termVariables(_) == NatType).map {
          id => id -> z3.mkConst(z3.mkStringSymbol(id.toString), i)
        })

      c.termEqualities.map {
        case (h1, h2) if isNatPredicate(c.termVariables, Primitive(Eq, Cons(h1, Cons(h2, Nil())))) =>
          solver.assertCnstr(z3Encode(z3, solver, z3Variables, Primitive(Eq, Cons(h1, Cons(h2, Nil())))))
        case _ => ()
      }

      val b = z3Encode(z3, solver, z3Variables, Primitive(Eq, Cons(t1, Cons(t2, Nil()))))
      solver.assertCnstr(z3.mkNot(b))

      c.variables.filter(c.termVariables(_) == NatType).map { id =>
        val v = z3.mkConst(z3.mkStringSymbol(id.toString), i)
        solver.assertCnstr(z3.mkGE(v, z3.mkInt(0, i)))
      }

      TypeChecker.z3Debug("Current Goal:\n" + g)
      TypeChecker.z3Debug("\nInvoking Z3\n")
      TypeChecker.z3Debug(solver.toString)

      val solverResponse = solver.check

      TypeChecker.z3Debug("Response: " + solverResponse + "\n")

      val modelString = solverResponse match {
        case scala.None => ""
        case scala.Some(true) => solver.getModel.toString
        case scala.Some(false) => ""
      }

      Solver.reclaim(factory)

      solverResponse match {
        case scala.None => Some((List(), _ => (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)}: Failure in Z3."))))
        case scala.Some(true) => Some((List(), _ => (false, ErrorJudgment(c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)}: Z3 found a counter-example: $modelString."))))
        case scala.Some(false) => Some((List(), _ => (true, AreEqualJudgment(c, t1, t2, "Validated by Z3"))))
      }

    case g =>
      None()
  }

  val NewReflexivity = Rule {
    case g @ EqualityGoal(c, t1, t2) if t1.isEqual(t2) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewReflexivity: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment(c, t1, t2, "By Reflexivity"))
        }
      ))
    case g =>
      None()
  }


  val NewSyntheseUnit = Rule {
    case g @ SynthesizeGoal(c, UnitType) =>
      Some((List(), _ => (true, SyntheseJudgment(c, UnitType, UnitLiteral))))
    case g =>
      None()
  }

  val NewSyntheseBool = Rule {
    case g @ SynthesizeGoal(c, BoolType) =>
      Some((List(), _ => (true, SyntheseJudgment(c, BoolType, BoolLiteral(true)))))
    case g =>
      None()
  }

  val NewSyntheseNat = Rule {
    case g @ SynthesizeGoal(c, NatType) =>
      Some((List(), _ => (true, SyntheseJudgment(c, NatType, NatLiteral(0)))))
    case g =>
      None()
  }

  val NewSyntheseVar = Rule {
    case g @ SynthesizeGoal(c, tp) if c.containsVarOfType(tp) =>
      Some((List(), _ => (true, SyntheseJudgment(c, NatType, Var(c.getVarOfType(tp).get)))))
    case g =>
      None()
  }

  val NewSynthesePi = Rule {
    case g @ SynthesizeGoal(c, tp @ PiType(tyX, Bind(x, ty))) =>
      val c1 = c.bind(x, tyX).incrementLevel
      val gb = SynthesizeGoal(c, ty)
      Some((
        List(_ => gb),
        {
          case Cons(SyntheseJudgment(_, _, t), _) =>
            (true, SyntheseJudgment(c, tp, Lambda(Some(tyX), Bind(x, t))))
          case _ =>
            (false, ErrorJudgment(c, s"Could not synthesize term of type ${typeOutput(tp)}."))
        }
      ))
    case _ => None()
  }

  val NewSyntheseSigma = Rule {
    case g @ SynthesizeGoal(c, tp @ SigmaType(ty1, Bind(id, ty2))) =>
      val g1 = SynthesizeGoal(c.incrementLevel, ty1)
      val fg2: List[Judgment] => Goal = {
        case Cons(SyntheseJudgment(_, _, t1), _) =>
          val c1 = c.incrementLevel.bind(id, t1)
          SynthesizeGoal(c1, ty2)
        case _ =>
          ErrorGoal(c, s"Could not synthesize term of type ${typeOutput(ty1)}.")
      }
      Some((
        List(_ => g1, fg2),
        {
          case Cons(SyntheseJudgment(_, _, t1), Cons(SyntheseJudgment(_, _, t2), _)) =>
            (true, SyntheseJudgment(c, tp, Pair(t1, t2)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not synthesize term of type ${typeOutput(tp)}."))
        }
      ))
    case _ => None()
  }

  val NewSyntheseSum = Rule {
    case g @ SynthesizeGoal(c, tp @ SumType(ty1, ty2)) =>
      val g1 = SynthesizeGoal(c.incrementLevel, ty1)
      val g2 = SynthesizeGoal(c.incrementLevel, ty1)
      Some((
        List(_ => g1, _ => g2),
        {
          case Cons(SyntheseJudgment(_, _, t1), _) =>
            (true, SyntheseJudgment(c, tp, LeftTree(t1)))
          case Cons(_, Cons(SyntheseJudgment(_, _, t2), _)) =>
            (true, SyntheseJudgment(c, tp, RightTree(t2)))
          case _ =>
            (false, ErrorJudgment(c, s"Could not synthesize term of type ${typeOutput(tp)}."))
        }
      ))
    case _ => None()
  }


}


object TypeChecker {
  import Rule._

  val tactic = (
    InferBool.t ||
    InferNat.t ||
    InferUnit.t ||
    InferVar.t ||
    InferLeft.t ||
    InferRight.t ||
    InferError.t ||
    InferLet.t ||
    InferPair.t ||
    InferFirst.t ||
    InferSecond.t ||
    InferApp.t ||
    InferLambda.t ||
    InferIf.t ||
    InferBinaryPrimitive.t ||
    InferUnaryPrimitive.t ||
    InferMatch.t ||
    InferEitherMatch.t ||
    InferFix.t || InferFixFail.t ||
    InferTypeAbs.t ||
    InferTypeApp.t ||
    InferForallInstantiation.t ||
    InferFold.t ||
    InferUnfold.t || NewInferUnfoldPositive.t ||
    InferFoldGen.t ||
    CheckVar.t ||
    CheckIf.t ||
    CheckMatch.t ||
    CheckEitherMatch.t ||
    CheckLet.t ||
    CheckLeft.t || CheckRight.t ||
    CheckIntersection.t ||
    CheckLambda.t || CheckPi.t ||
    CheckPair.t || CheckSigma.t ||
    CheckRefinement.t ||
    CheckTypeAbs.t ||
    CheckRecursive.t ||
    CheckTop1.t ||
    CheckTop2.t ||
    CheckReflexive.t ||
    NewReflexivity.t ||
    NewEqualityInContext.t ||
    NewUnfoldRefinementInContext.t ||
    NewUseContextEqualities.t ||
    NewApplyValueSimplification.t ||
    NewApplyTopLevelSimplification.t ||
    NewTopIf.t ||
    NewTopMatch.t ||
    NewContradiction.t ||
    NewZ3ArithmeticSolver.t ||
    UnsafeIgnoreEquality.t ||
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    FailRule.t
  ).repeat

  val tdebug = false
  val edebug = false
  val zdebug = false

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context(List(), Map(), Set(), List(), 0, max), t)
    tactic.apply(g, sg => None())
  }

  def inferInContext(c: Context, t: Tree) = {
    val g = InferGoal(c, t)
    tactic.apply(g, sg => None())
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
