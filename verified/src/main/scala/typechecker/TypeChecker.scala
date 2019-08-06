package typechecker

import _root_.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import Derivation._

case class Context(
  val variables: List[Identifier],
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Tree],
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

  def bindFresh(s: String, t: Tree) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree) = copy(termEqualities = (t1, t2)::termEqualities)

  def incrementLevel() = copy(level = level + 1)

  override def toString: String = {
    /*"Term equalities:\n" ++
    termEqualities.foldLeft("") {
      case (acc, (a, b)) => acc + s"${a} = ${b}\n"
    } ++ "Term variables:\n" ++
    variables.foldLeft("") {
      case (acc, id) => acc + s"${id}: ${termVariables(id)}\n"
    }*/
    ""
  }

  def containsVarEqualities: Boolean = {
    termEqualities.exists {
      case (Var(_), _) => true
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
}

sealed abstract class Goal {
  val c: Context
}

case class InferGoal(c: Context, t: Tree) extends Goal {
  override def toString: String = {
    s"Inferring $t"
  }
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  override def toString: String = {
    s"Checking ${t}: ${tp}"
  }
}

case class SynthesizeGoal(c: Context, tp: Tree) extends Goal

case class EqualityGoal(c: Context, t1: Tree, t2: Tree) extends Goal {
  override def toString: String = {
    s"Check equality ${t1} = ${t1}"
  }
}

case class ErrorGoal(c: Context, s: String) extends Goal {
  val level = 0

  override def toString: String = {
    s"Error Goal : ${s}"
  }
}

object TypeOperators {
  private def binop(t1: Tree, t2: Tree, f: (Tree, Tree) => Tree): Option[Tree] = {
    (t1, t2) match {
      case (UnitType, UnitType) => Some(UnitType)
      case (NatType, NatType) => Some(NatType)
      case (BoolType, BoolType) => Some(BoolType)
      case (TopType, TopType) => Some(TopType)
      case (SumType(t11, t12), SumType(t21, t22)) =>
        binop(t11, t21, f).flatMap { t1 =>
          binop(t12, t22, f).map { t2 =>
            SumType(t1, t2)
          }
        }
      case (PiType(a1, Bind(x, b1)), PiType(a2, Bind(x2, b2))) =>
        binop(a1, a2, f).flatMap { a =>
          binop(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            PiType(a, Bind(x, b))
          }
        }
      case (IntersectionType(a1, Bind(x, b1)), IntersectionType(a2, Bind(x2, b2))) =>
        binop(a1, a2, f).flatMap { a =>
          binop(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            IntersectionType(a, Bind(x, b))
          }
        }
      case (PolyForallType(Bind(x, b1)), PolyForallType(Bind(x2, b2))) =>
        binop(b1, Tree.replace(x2, Var(x), b2), f).map(b =>
          PolyForallType(Bind(x, b))
        )
      case (SigmaType(a1, Bind(x, b1)), SigmaType(a2, Bind(x2, b2))) =>
        binop(a1, a2, f).flatMap { a =>
          binop(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            SigmaType(a, Bind(x, b))
          }
        }
      case (RefinementType(a1, Bind(x, p1)), RefinementType(a2, Bind(x2, p2))) =>
        binop(a1, a2, f).map { a =>
          RefinementType(a, Bind(x, f(p1, Tree.replace(x2, Var(x), p2))))
        }
      case (RefinementType(a1, Bind(x, p1)), t3) =>
        binop(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (t3, RefinementType(a1, Bind(x, p1))) =>
        binop(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (EqualityType(t11, t12), EqualityType(t21, t22)) =>
        Some(EqualityType(f(t11, t21), f(t12, t22)))
      case (_, _) => None()
    }
  }

  def ifThenElse(tc: Tree, t1: Tree, t2: Tree): Option[Tree] = {
    if (t1 == t2) Some(t1)
    else binop(t1, t2, (ty1: Tree, ty2: Tree) => IfThenElse(tc, ty1, ty2))
  }

  def matchSimpl(n: Tree, t0: Tree, id: Identifier, tn: Tree): Option[Tree] = {
    binop(t0, tn, (ty0: Tree, tyn: Tree) => Match(n, ty0, Bind(id, tyn)))
  }

  def eitherMatch(n: Tree, idl: Identifier, tl: Tree, idr: Identifier, tr: Tree): Option[Tree] = {
    binop(tl, tr, (tyl: Tree, tyr: Tree) => EitherMatch(n, Bind(idl, tyl), Bind(idr, tyr)))
  }

  def letIn(x: Identifier, tp: Option[Tree], v: Tree, t: Tree) = {
    def f(t1: Tree, t2: Tree): Tree = {
      if (x.isFreeIn(t1)) LetIn(tp, v, Bind(x, t1))
      else t1
    }
    binop(t, t, f)
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
}

case class Tactic[T](apply: (Goal, (Goal => Option[T])) => Option[T]) {
  def ||(other: Tactic[T]): Tactic[T] = this.or(other)
  def or(other: Tactic[T]): Tactic[T] =
    Tactic {
      case (g, subgoalSolver) =>
        apply(g, subgoalSolver).orElse(
          other.apply(g, subgoalSolver)
        )
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
              accOpt.flatMap {
                case (success, acc) =>
                  subgoalSolver(fsg(acc.map(_.node))).map { case (subSuccess: Boolean, subTree: NodeTree[Judgment]) =>
                    (success && subSuccess, acc :+ subTree)
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

  def unzip[A,B](l: List[(A,B)]): (List[A], List[B]) = l match {
    case Nil() => (Nil(), Nil())
    case Cons((a,b), xs) =>
      val (as, bs) = unzip(xs)
      (Cons(a, as), Cons(b, bs))
  }

  val InferBool = Rule {
    case g @ InferGoal(c, BoolLiteral(b)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferBool : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((
        List(),
        _ => (true, InferJudgment(c, BoolLiteral(b), Some(BoolType)))
      ))
    case g =>
      None()
  }

  val InferNat = Rule {
    case g @ InferGoal(c, NatLiteral(n)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferNat : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment(c, NatLiteral(n), Some(NatType)))))
    case g =>
      None()
  }

  val InferUnit = Rule {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferUnit : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment(c, UnitLiteral, Some(UnitType)))))
    case g =>
      None()
  }

  val InferVar = Rule {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferVar : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None() => (false, ErrorJudgment(c, InferJudgment(c, Var(id), None())))
          case Some(tpe) => (true, InferJudgment(c, Var(id), Some(tpe)))
        }
      ))

    case g =>
      None()
  }

  val InferError = Rule {
    case g @ InferGoal(c, e @ ErrorTree(_, Some(tp))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferError : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val errorGoal = EqualityGoal(c.incrementLevel(), BoolLiteral(false), BoolLiteral(true))
      Some((List(_ => errorGoal),
        {
          case Cons(AreEqualJudgment(_, _, _), _) => (true, InferJudgment(c, e, Some(tp)))
          case _ => (false, ErrorJudgment(c, InferJudgment(c, e, Some(tp))))
        }
      ))

    case g =>
      None()
  }

  val InferLet = Rule {
    case g @ InferGoal(c, e @ LetIn(None(), v, Bind(id, body))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, Some(tyv)), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c, s"Could not infer type for $v")
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
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _), Cons(InferJudgment(_, _, Some(tyb)), _)) =>
            (true, InferJudgment(c, e, Some(tyb)))
          case _ =>
            (false, ErrorJudgment(c, InferJudgment(c, e, None())))
        }
      ))

    case g =>
      None()
  }

  val InferLambda = Rule {
    case InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case Cons(InferJudgment(_, _, Some(tyb)), _) =>
            (true, InferJudgment(c, e, Some(PiType(ty1, Bind(id, tyb)))))
          case _ =>
            (false, ErrorJudgment(c, InferJudgment(c, e, None())))
        }
      ))

    case g =>
      None()
  }

  val InferIf = Rule {
    case InferGoal(c, e @ IfThenElse(tc, t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BoolLiteral(true))
      val c2 = c0.addEquality(tc, BoolLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val inferT1 = InferGoal(c1, t1)
      val inferT2 = InferGoal(c2, t2)
      Some((
        List(_ => checkCond, _ => inferT1, _ => inferT2),
        {
          case Cons(CheckJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(InferJudgment(_, _, Some(ty2)),
            _
          ))) =>
            TypeOperators.ifThenElse(tc, ty1, ty2) match {
              case None() => (false, ErrorJudgment(c, s"Could not unify types $ty1 and $ty2"))
              case Some(ty) => (true, InferJudgment(c, e, Some(ty)))
            }

          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))

    case g =>
      None()
  }

  val InferBinaryPrimitive = Rule {
    case InferGoal(c, e @ Primitive(op, Cons(n1, Cons(n2, Nil())))) if op.isBinOp =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferBinaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c, n1, opType)
      val checkN2 = CheckGoal(c, n2, opType)
      Some((
        List(_ => checkN1, _ => checkN2),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) =>
            (true, InferJudgment(c, e, Some(op.returnedType)))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferUnaryPrimitive = Rule {
    case InferGoal(c, e @ Primitive(op, Cons(n1, Nil()))) if op.isUnOp =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferUnaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c, n1, opType)
      Some((
        List(_ => checkN1),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, InferJudgment(c, e, Some(op.returnedType)))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferMatch = Rule {
    case InferGoal(c, e @ Match(t, t0, Bind(id, tn))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
              case None() => (false, ErrorJudgment(c, s"Could not unify types $ty0 and $tyn."))
              case Some(ty) => (true, InferJudgment(c, e, Some(ty)))
            }

          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferEitherMatch = Rule {
    case InferGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val finferT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c, s"Expecting a sum type for $t, found $ty.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for $t.")
      }
      val finferT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, s"Expecting a sum type for $t, found $ty.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for $t.")
      }
      Some((
        List(_ => inferScrutinee, finferT1, finferT2), {
          case Cons(InferJudgment(_, _, _),
            Cons(InferJudgment(_, _, Some(ty1)),
            Cons(InferJudgment(_, _, Some(ty2)), _
          ))) =>
            TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
              case None() => (false, ErrorJudgment(c, s"Could not unify types $ty1 and $ty2."))
              case Some(ty) => (true, InferJudgment(c, e, Some(ty)))
            }

          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferFix = Rule {
    case InferGoal(c, e @ Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferFix : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")

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
            (true, InferJudgment(c, e, Some(IntersectionType(NatType, Bind(n, ty)))))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferForallInstantiation = Rule {
    case InferGoal(c, e @ Inst(t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferForallInstantiation : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case IntersectionType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting an intersection type for $t1, found $ty.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for $t1.")
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, Some(ty)),
            Cons(CheckJudgment(_, _, _), _)) =>

            dropRefinements(ty) match {
              case IntersectionType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() => (false, ErrorJudgment(c, s"Error in letIn($x, $t2, $ty)"))
                  case Some(t) => (true, InferJudgment(c, e, Some(t)))
                }
              case _ => (false, ErrorJudgment(c, s"Expecting an intersection type for $t1, found $ty."))
            }

          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val InferApp = Rule {
    case InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferApp : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting a pi type for $t1, found $ty.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for $t1.")
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, Some(ty)),
            Cons(CheckJudgment(_, _, _), _)) =>

            dropRefinements(ty) match {
              case PiType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() => (false, ErrorJudgment(c, s"Error in letIn($x, $t2, $ty)"))
                  case Some(t) => (true, InferJudgment(c, e, Some(t)))
                }
              case _ => (false, ErrorJudgment(c, s"Expecting a pi type for $t1, found $ty."))
            }

          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val UnsafeIgnoreEquality = Rule {
    case EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug(s"Context:\n${c}\n")
      TypeChecker.equalityDebug(s"Ignoring equality ${t1} = ${t2}.\n\n")
      Some(List(), _ => (true, AreEqualJudgment(c, t1, t2)))
    case g =>
      None()
  }

  val CatchErrorGoal = Rule {
    case ErrorGoal(c, s) =>
      Some(List(), _ => (false, ErrorJudgment(c, s)))
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
    case CheckGoal(c, t, tpe @ RefinementType(ty, Bind(id, b))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckRefinement : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val checkTy = CheckGoal(c, t, ty)
      val c1 = c.bind(id, ty).addEquality(Var(id), t)
      val checkRef = EqualityGoal(c1, b, BoolLiteral(true))
      Some((
        List(_ => checkTy, _ => checkRef), {
          case Cons(CheckJudgment(_, _, _), Cons(AreEqualJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, t))
        }
      ))

    case _ => None()
  }

  val CheckReflexive = Rule {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckReflexive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gInfer = InferGoal(c.incrementLevel(), t)
      Some((List(_ => gInfer),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) if (dropRefinements(tpe) == ty) =>
            (true, CheckJudgment(c, t, ty))
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (false, ErrorJudgment(c, s"Expecting type $ty for $t, found $tpe"))
          case _ =>
            (false, ErrorJudgment(c, s"Could not infer a type for $t"))
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
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferPair : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val inferFirst = InferGoal(c.incrementLevel, t1)
        val inferSecond = InferGoal(c.incrementLevel, t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case Cons(InferJudgment(_, _, Some(ty1)), Cons(InferJudgment(_, _, Some(ty2)), _)) =>
            val inferedType = SigmaType(ty1, Bind(Identifier(0, "X"), ty2))
            (true, InferJudgment(c, e, Some(inferedType)))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))
    case g =>
      None()
  }

  val InferFirst = Rule {
    case g @ InferGoal(c, e @ First(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferFirst : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(SigmaType(ty, _))), _) =>
            (true, InferJudgment(c, e, Some(ty)))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))
    case g =>
      None()
  }

  val InferSecond = Rule {
    case g @ InferGoal(c, e @ Second(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferSecond : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(SigmaType(_, Bind(x, ty)))), _) =>
            TypeOperators.letIn(x, None(), First(t), ty) match {
                  case None() => (false, ErrorJudgment(c, s"Error in letIn($x, ${First(t)}, $ty)"))
                  case Some(t) => (true, InferJudgment(c, e, Some(t)))
                }
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))
    case g =>
      None()
  }

  val InferLeft = Rule {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (true, InferJudgment(c, e, Some(SumType(tpe, BottomType))))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))
    case g =>
      None()
  }

  val InferRight = Rule {
    case g @ InferGoal(c, e @ RightTree(t)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, Some(tpe)), _) =>
            (true, InferJudgment(c, e, Some(SumType(BottomType, tpe))))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))
    case g =>
      None()
  }

  val CheckLeft = Rule {
    case g @ CheckGoal(c, e @ LeftTree(t), tpe @ SumType(ty, _)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel, t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, t))
        }
      ))
    case g =>
      None()
  }

  val CheckRight = Rule {
    case g @ CheckGoal(c, e @ RightTree(t), tpe @ SumType(_, ty)) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel, t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, t))
        }
      ))
    case g =>
      None()
  }

  val CheckPi = Rule {
    case g @ CheckGoal(c, e @ t, tpe @ PiType(ty1, Bind(id,ty2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckPi : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel, App(t, Var(freshId)), ty2)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _), _) =>
            (true, CheckJudgment(c, e, tpe))
          case _ =>
            (false, ErrorJudgment(c, t))
        }
      ))
    case g =>
      None()
  }

  val CheckIf = Rule {
    case CheckGoal(c, e @ IfThenElse(tc, t1, t2), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            Cons(InferJudgment(_, _, _),
            _
          ))) =>
            (true, CheckJudgment(c, e, ty))
          case _ =>
            (false, ErrorJudgment(c, e))
        }
      ))

    case g =>
      None()
  }

  val CheckMatch = Rule {
    case CheckGoal(c, e @ Match(t, t0, Bind(id, tn)), ty) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckkMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val CheckEitherMatch = Rule {
    case CheckGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), tpe) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val fcheckT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, tpe)
            case _ => ErrorGoal(c, s"Expecting a sum type for $t, found $ty.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for $t.")
      }
      val fcheckT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, Some(ty)), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              CheckGoal(c2, t2, tpe)
            case _ => ErrorGoal(c, s"Expecting a sum type for $t, found $ty.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for $t.")
      }
      Some((
        List(_ => inferScrutinee, fcheckT1, fcheckT2), {
          case Cons(InferJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _),
            Cons(CheckJudgment(_, _, _), _
          ))) =>
            (true, CheckJudgment(c, e, tpe))

          case _ => (false, ErrorJudgment(c, e))
        }
      ))

    case _ => None()
  }

  val CheckSigma = Rule {
    case g @ CheckGoal(c, t, tpe @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckSigma : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val checkFirst = CheckGoal(c.incrementLevel, First(t), ty1)
        val c1 = c.bind(id, ty2).addEquality(Var(id), First(t)).incrementLevel
        val checkSecond = CheckGoal(c1, Second(t), ty2)
      Some((List(_ => checkFirst, _ => checkSecond),
        {
          case Cons(CheckJudgment(_, _, _), Cons(CheckJudgment(_, _, _), _)) =>
            (true, CheckJudgment(c, t, tpe))
          case _ =>
            (false, ErrorJudgment(c, t))
        }
      ))
    case g =>
      None()
  }

}


/*


case object CheckLet extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, LetIn(None(), v, Bind(id, body)), ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val gv = InferGoal(c, v)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(tyv)) =>
              val c1 = c.bind(id, tyv).addEquality(Var(id), v)
              CheckGoal(c1, body, ty)
            case _ => ErrorGoal(c,  s"Error in CheckLet ${g}")
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, fgb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(fgb(rc)) match {
              case Some(InferResult(ty)) => rc.updateResults(g, InferResult(ty))
              case _ => rc
            }
          }
        )
      case CheckGoal(c, LetIn(Some(tyv), v, Bind(id, body)), ty, l) =>
        val gv = CheckGoal(c, v, tyv)
        val c1 = c.addEquality(Var(id), v)
        val gb = CheckGoal(c1, body, ty)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, (rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(gv), rc.results.get(gb)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true))) => rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object CheckIntersection extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, t, IntersectionType(tyid, Bind(id, ty)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal CheckIntersection : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val (freshId, c1) = c.bindFresh(id.name, tyid)
        val subgoal = CheckGoal(c1, Inst(t, Var(freshId)), ty)
        ResultGoalContext(
          List((r: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
             rc.results.get(subgoal) match {
              case Some(CheckResult(true)) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferDropRefinement extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    g match  {
      case InferGoal(c, t, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal InferDropRefinement : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val inferGoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => inferGoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(inferGoal) match {
              case Some(InferResult(RefinementType(ty, _))) => rc.updateResults(g, InferResult(ty))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NoName1Resolve extends Rule {
  def replace(c: Context, t: Tree): Tree = {
    val t1 = c.termEqualities.foldLeft(t) { case (acc, (v1, v2)) =>
      v1 match {
        case Var(id) => Tree.replace(id, v2, acc)
        case _ => acc
      }
    }
    t1
  }



  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, t1, t2, l) if c.containsVarEqualities =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"Use term equalities context and replace variables.")
        val newT1 = replace(c, t1)
        val newT2 = replace(c, t2)
        TypeChecker.equalityDebug(s"=> Should show ${newT1} = ${newT2}.\n\n")
        val c1 = c.copy(termEqualities = c.termEqualities.filterNot {
          case (Var(_), _) => true
          case (_, _) => false
        })
        val subgoal = EqualityGoal(c1, newT1, newT2)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(EqualityResult(true)) => rc.updateResults(g, EqualityResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NoName2Resolve extends Rule {
  def replace(c: Context, t: Tree): Context = {
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
    /* SHould be applied more than once
       For now Id issues => not possible
    */
  }

  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, t1, t2, l) if c.hasRefinementBound =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"Unfold refinement types to obtain predicates and types.\n\n")
        val c1 = replace(c, t1)
        val c2 = replace(c1, t2)
        val subgoal = EqualityGoal(c1, t1, t2, l + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(EqualityResult(true)) => rc.updateResults(g, EqualityResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object ReplaceLet extends Rule {
  def apply(g: Goal): ResultGoalContext = {
   g match {
      case EqualityGoal(c, LetIn(tp, v, Bind(x, t1)), t2, l) =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${LetIn(tp, v, Bind(x, t1))} = ${t2}")
        TypeChecker.equalityDebug(s"Set ${x} = ${v} in context.\n\n")
        val c1 = c.addEquality(Var(x), v)
        val subgoal =  EqualityGoal(c1, t1, t2)
          ResultGoalContext(
            List((rc: ResultGoalContext) => subgoal),
            Map(),
            (rc: ResultGoalContext) =>
              rc.results.get(subgoal) match {
                case Some(EqualityResult(true)) => rc.updateResults(g, EqualityResult(true))
                case _ => rc
              }
          )
      case _ => errorContext
    }
  }
}



case object InContextResolve extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, t1, t2, l) if c.termEqualities.contains((t1, t2)) =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"By assumption : ${t1} = ${t2} in context.\n\n")
          ResultGoalContext(
            Nil(),
            Map(g -> EqualityResult(true)),
            (rc: ResultGoalContext) => { rc.updateResults(g, EqualityResult(true)) }
          )
      case _ => errorContext
    }
  }
}

case object ReflexivityResolve extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, t1, t2, l) if t1 == t2 =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"By reflexivity. Qed\n\n")
          ResultGoalContext(
            Nil(),
            Map(g -> EqualityResult(true)),
            (rc: ResultGoalContext) => { rc.updateResults(g, EqualityResult(true)) }
          )
      case _ => errorContext
    }
  }
}

case object GoodArithmeticResolve extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, Primitive(Lt, Cons(n1, Cons(Primitive(Plus, Cons(n2, Cons(NatLiteral(n3), Nil()))), Nil()))), t2, l) if n1 == n2 && n3 > 0 =>
        val t1 = Primitive(Lt, Cons(n1, Cons(Primitive(Plus, Cons(n2, Cons(NatLiteral(n3), Nil()))), Nil())))
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"(${n1} < ${n2} + ${n3}) holds => should show true = ${t2}.\n\n")
        val subgoal =  CheckGoal(c, n1, NatType)
        val subgoal2 = (rc: ResultGoalContext) => {
          rc.results.get(subgoal) match {
            case Some(CheckResult(true)) => EqualityGoal(c, BoolLiteral(true), t2, l + 1)
            case _ => ErrorGoal(c, s"Error in GoodArithmeticResolve ${g}")
          }
        }
          ResultGoalContext(
            List((rc: ResultGoalContext) => subgoal, subgoal2),
            Map(),
            (rc: ResultGoalContext) =>
              rc.results.get(subgoal2(rc)) match {
                case Some(EqualityResult(true)) => rc.updateResults(g, EqualityResult(true))
                case _ => rc
              }
          )
      case _ => errorContext
    }
  }
}


case object NatInequalityResolve extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, Primitive(Lt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil()))), t2, l)  =>
        val t1 = Primitive(Lt, Cons(NatLiteral(n1), Cons(NatLiteral(n2), Nil())))
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Should show ${t1} = ${t2}.")
        TypeChecker.equalityDebug(s"(${n1} < ${n2}) = ${n1 < n2} => should show ${n1 < n2} = ${t2}.\n\n")
        val subgoal = EqualityGoal(c, BoolLiteral(n1 < n2), t2, l + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) =>
            rc.results.get(subgoal) match {
              case Some(EqualityResult(true)) => rc.updateResults(g, EqualityResult(true))
              case _ => rc
            }
        )
      case _ => errorContext
    }
  }
}

case object InferFold extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Fold(Some(RecType(n, Bind(a, ty))), t), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferFold : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkN = CheckGoal(c, n, NatType, l + 1)
        val c1 = c.addEquality(n, NatLiteral(0))
        val checkBase = CheckGoal(c1, t, TypeSimplification.basetype(a, ty), l + 1)
        val (id, c2) = c.bindFresh("_n", NatType)
        val n2 = Var(id)
        val c3 = c.addEquality(
          n2,
          Primitive(Plus, List(n, NatLiteral(1)))
        )
        val nTy = RecType(n2, Bind(a, ty))
        val check = CheckGoal(c3, t, Tree.replace(a, nTy, ty), l + 1)
        ResultGoalContext(
          List(
            (r: ResultGoalContext) => checkN,
            (r: ResultGoalContext) => checkBase,
            (r: ResultGoalContext) => check
          ),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkN), rc.results.get(checkBase), rc.results.get(check)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true)), Some(CheckResult(true))) =>
                rc.updateResults(g, InferResult(RecType(n, Bind(a, ty))))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}
}

*/


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
    InferFix.t ||
    InferForallInstantiation.t ||
    CheckLeft.t ||
    CheckRight.t ||
    CheckPi.t ||
    CheckIf.t ||
    CheckMatch.t ||
    CheckEitherMatch.t ||
    CheckSigma.t ||
    CheckRefinement.t ||
    CheckReflexive.t ||
    UnsafeIgnoreEquality.t ||
    CatchErrorGoal.t ||
    FailRule.t
  ).repeat

  val tdebug = false
  val edebug = false

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context(List(), Map(), Set(), List(), max, 0), t)
    tactic.apply(g, sg => None())
  }

  def typeCheckDebug(s: String): Unit = {
    if (tdebug) println(s)
  }

  def equalityDebug(s: String): Unit = {
    if (edebug) println(s)
  }
}
