package verified
package typechecker

import verified.trees._
import verified.solver._

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.io.StdOut.println

import z3.scala._

import Derivation._
import Util._

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
    if (variables.contains(i)) throwException("Already bound " + i.toString)
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

  @extern override def toString: String = {
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


sealed abstract class Goal {
  val c: Context

  def replace(id: Identifier, t: Tree): Goal

  def updateContext(c: Context): Goal
}

case class InferGoal(c: Context, t: Tree) extends Goal {
  @extern override def toString: String = {
    s"Inferring $t"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    InferGoal(c.replace(id, t1), t.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  @extern override def toString: String = {
    s"Checking ${t}: ${tp}"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    CheckGoal(c.replace(id, t1), t.replace(id, t1), tp.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class SynthesisGoal(c: Context, tp: Tree) extends Goal {
  def replace(id: Identifier, t: Tree): Goal = {
    SynthesisGoal(c.replace(id, t), tp.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EqualityGoal(c: Context, t1: Tree, t2: Tree) extends Goal {
  @extern override def toString: String = {
    s"Check equality ${t1} ≡ ${t2}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EqualityGoal(c.replace(id, t), t1.replace(id, t), t2.replace(id, t))
  }

  def updateContext(newC: Context): Goal = {
    copy(c = newC)
  }
}

case class ErrorGoal(c: Context, s: String) extends Goal {
  val level = 0

  @extern override def toString: String = {
    s"Error Goal: ${s}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    ErrorGoal(c.replace(id, t), s)
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EmptyGoal(c: Context) extends Goal {

  @extern override def toString: String = {
    s"No Goal"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    EmptyGoal(c.replace(id, t))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
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

  def repeat(n: Int): Tactic[A,B] = {
    def repeatApply(n: Int, goal: A, subgoalSolver: A => Option[B]): Option[B] = {
      if (n <= 0) None()
      else apply(goal, sg => repeatApply(n-1, sg, subgoalSolver))
    }
    Tactic[A,B]((goal, subgoalSolver) => repeatApply(n, goal, subgoalSolver))
  }
}

case class Rule(
  apply: Goal => Option[(
    List[List[Judgment] => Goal],
    List[Judgment] => (Boolean, Judgment))
  ]) {
  def t: Tactic[Goal, (Boolean, NodeTree[Judgment])] = Tactic { (g, subgoalSolver) =>
    apply(g).flatMap {
      case (sgs, merge) =>
        val subTrees: Option[(Boolean, List[NodeTree[Judgment]])] =
          sgs.foldLeft[Option[(Boolean, List[NodeTree[Judgment]])]](Some(true, List())) {
            case (accOpt, fsg) =>
              accOpt.flatMap {
                case (success, acc) =>
                  subgoalSolver(fsg(acc.map(_.node))).map {
                    case (subSuccess, subTree) =>
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

  @extern private def termOutput(t: Tree): String =
    Derivation.termColor(Derivation.shortString(t.toString))

  @extern private def typeOutput(t: Tree): String =
    Derivation.typeColor(Derivation.shortString(t.toString))

  @extern private def bold(s: String): String = Derivation.bold(s)

  val InferBool = Rule {
    case g @ InferGoal(c, BooleanLiteral(b)) =>
      TypeChecker.debugs(g, "InferBool")
      Some((
        List(),
        _ => (true, InferJudgment("InferBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None()
  }

  val CheckBool = Rule {
    case g @ CheckGoal(c, BooleanLiteral(b), BoolType) =>
      TypeChecker.debugs(g, "CheckBool")
      Some((
        List(),
        _ => (true, CheckJudgment("CheckBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None()
  }

  val InferNat = Rule {
    case g @ InferGoal(c, NatLiteral(n)) =>
      TypeChecker.debugs(g, "InferNat")
      Some((List(), _ => (true, InferJudgment("InferNat", c, NatLiteral(n), NatType))))
    case g =>
      None()
  }

  val CheckNat = Rule {
    case g @ CheckGoal(c, NatLiteral(n), NatType) =>
      TypeChecker.debugs(g, "CheckNat")
      Some((List(), _ => (true, CheckJudgment("CheckNat", c, NatLiteral(n), NatType))))
    case g =>
      None()
  }

  val InferUnit = Rule {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.debugs(g, "InferUnit")
      Some((List(), _ => (true, InferJudgment("InferUnit", c, UnitLiteral, UnitType))))
    case g =>
      None()
  }

  val CheckUnit = Rule {
    case g @ CheckGoal(c, UnitLiteral, UnitType) =>
      TypeChecker.debugs(g, "CheckUnit")
      Some((List(), _ => (true, CheckJudgment("CheckUnit", c, UnitLiteral, UnitType))))
    case g =>
      None()
  }

  val InferVar = Rule {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.debugs(g, "InferVar")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None() => (false, ErrorJudgment("InferVar", c, id.toString + " is not in context"))
          case Some(tpe) => (true, InferJudgment("InferVar", c, Var(id), tpe))
        }
      ))

    case g =>
      None()
  }

  val CheckVar = Rule {
    case g @ CheckGoal(c, Var(id), ty) if c.termVariables.getOrElse(id, UnitLiteral).isEqual(ty) =>
      TypeChecker.debugs(g, "CheckVar")
      Some((List(), _ => (true, CheckJudgment("CheckVar", c, Var(id), ty))))
    case g =>
      None()
  }

  val InferError = Rule {
    case g @ InferGoal(c, e @ Error(_, Some(tp))) =>
      TypeChecker.debugs(g, "InferError")
      val errorGoal = EqualityGoal(c.incrementLevel(), BooleanLiteral(false), BooleanLiteral(true))
      Some((List(_ => errorGoal),
        {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) => (true, InferJudgment("InferError", c, e, tp))
          case _ => (false, ErrorJudgment("InferError", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferLet = Rule {
    case g @ InferGoal(c, e @ LetIn(None(), v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, tyv), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c, "Could not infer type for " + termOutput(v) + " so we didn't type check the rest.")
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(InferJudgment(_, _, _, tyb), _)) =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, anyToString(g)))
        }
      ))

    case g @ InferGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(InferJudgment(_, _, _, tyb), _)) =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferLambda = Rule {
    case g @ InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLambda")
      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case Cons(InferJudgment(_, _, _, tyb), _) =>
            (true, InferJudgment("InferLambda", c, e, PiType(ty1, Bind(id, tyb))))
          case _ =>
            // Returning Top is sound but a bit misleading
            // (true, InferJudgment(c, e, TopType))
            (false, ErrorJudgment("InferLambda", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferErasableLambda = Rule {
    case g @ InferGoal(c, e @ ErasableLambda(ty1, Bind(id, body))) if !id.isFreeIn(body.erase) =>
      TypeChecker.debugs(g, "InferErasableLambda")

      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case Cons(InferJudgment(_, _, _, tyb), _) =>
            (true, InferJudgment("InferErasableLambda", c, e, IntersectionType(ty1, Bind(id, tyb))))
          case _ =>
            (false, ErrorJudgment("InferErasableLambda", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferIf = Rule {
    case g @ InferGoal(c, e @ IfThenElse(tc, t1, t2)) =>
      TypeChecker.debugs(g, "InferIf")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BooleanLiteral(true))
      val c2 = c0.addEquality(tc, BooleanLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val inferT1 = InferGoal(c1, t1)
      val inferT2 = InferGoal(c2, t2)
      Some((
        List(_ => checkCond, _ => inferT1, _ => inferT2),
        {
          case Cons(CheckJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty1),
            Cons(InferJudgment(_, _, _, ty2),
            _
          ))) =>
            TypeOperators.ifThenElse(tc, ty1, ty2) match {
              case None() => (false,
                ErrorJudgment(
                  "InferIf",
                  c,
                  "Could not infer type for " + termOutput(e) + " with InferIf: cannot unify " +
                  typeOutput(ty1) +  " and  " + typeOutput(ty2)
                )
              )
              case Some(ty) =>
                (true, InferJudgment("InferIf", c, e, ty))
            }

          case _ =>
            (false, ErrorJudgment("InferIf", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferBinaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Cons(n2, Nil())))) if op.isBinOp =>
      TypeChecker.debugs(g, "InferBinaryPrimitive")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel(), n1, opType)
      val checkN2 = CheckGoal(c.incrementLevel(), n2, opType)
      val checkEq = EqualityGoal(c.incrementLevel(), Primitive(Gteq, List(n1, n2)), BooleanLiteral(true))
      Some((
        if(op == Minus) List(_ => checkN1, _ => checkN2, _ => checkEq) else List(_ => checkN1, _ => checkN2),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _))) =>
            (true, InferJudgment("InferBinaryPrimitive", c, e, NatType))
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) if op != Minus =>
            (true, InferJudgment("InferBinaryPrimitive", c, e, op.returnedType))
          case _ =>
            (false, ErrorJudgment("InferBinaryPrimitive", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferUnaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Nil()))) if op.isUnOp =>
      TypeChecker.debugs(g, "InferUnaryPrimitive")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel(), n1, opType)
      Some((
        List(_ => checkN1),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, InferJudgment("InferUnaryPrimitive", c, e, op.returnedType))
          case _ =>
            (false, ErrorJudgment("InferUnaryPrimitive", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferMatch = Rule {
    case g @ InferGoal(c, e @ Match(t, t0, Bind(id, tn))) =>
      TypeChecker.debugs(g, "InferMatch")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val inferT0 = InferGoal(c0, t0)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val inferTn = InferGoal(cn, tn)
      Some((
        List(_ => checkN, _ => inferT0, _ => inferTn), {
          case Cons(CheckJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty0),
            Cons(InferJudgment(_, _, _, tyn), _
          ))) =>
            TypeOperators.matchSimpl(t, ty0, id, tyn) match {
              case None() => (false,
                ErrorJudgment(
                  "InferMatch",
                  c,
                  "Cannot unify types " + typeOutput(ty0) + " and " + typeOutput(tyn)
                )
              )
              case Some(ty) => (true, InferJudgment("InferMatch", c, e, ty))
            }

          case _ =>
            (false, ErrorJudgment("InferMatch", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferEitherMatch = Rule {
    case g @ InferGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
      TypeChecker.debugs(g, "InferEitherMatch")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)

      val finferT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) +  ", found " + typeOutput(ty) + ",  we didn't typecheck the body of either_match")
          }
        case _ => ErrorGoal(c, "Could not infer a type for " + termOutput(t) + " then we didn't typecheck the body of either_match")
      }

      val finferT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) +  ", found " + typeOutput(ty) + ",  we didn't typecheck the body of either_match")
          }
        case _ => ErrorGoal(c, "Could not infer a type for " + termOutput(t) + " then we didn't typecheck the body of either_match")
      }

      Some((
        List(_ => inferScrutinee, finferT1, finferT2), {
          case Cons(InferJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty1),
            Cons(InferJudgment(_, _, _, ty2), _))) =>
              TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
                case None() => (false, ErrorJudgment("InferEitherMatch", c, "Could not unify the types " + typeOutput(ty1) + " " + typeOutput(ty2)))
                case Some(ty) => (true, InferJudgment("InferEitherMatch", c, e, ty))
              }

          case _ => (false, ErrorJudgment("InferEitherMatch", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferFix = Rule {
    case g @ InferGoal(c, e @ Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) if !n1.isFreeIn(t.erase) =>
      TypeChecker.debugs(g, "InferFix")

      val (freshM, c0) = c.incrementLevel().getFresh("_M")
      val (freshN, c1) = c0.bindFresh(n1.name, NatType)
      val (freshY, c2) = c1.bindFresh(y.name,
        PiType(UnitType, Bind(Identifier(0, "_"),
          IntersectionType(
            RefinementType(NatType, Bind(freshM, Primitive(Lt, List(Var(freshM), Var(freshN))))),
            Bind(freshM, ty.replace(n, Var(freshM)))
          )
        ))
      )
      val c3 = c2.addEquality(
        Var(freshY),
        Lambda(Some(UnitType), Bind(Identifier(0, "_Unit"), e))
      )
      Some((
        List(_ => CheckGoal(c3, t.replace(n1, freshN).replace(y, freshY), ty.replace(n, freshN))), {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, InferJudgment("InferFix", c, e, IntersectionType(NatType, Bind(n, ty))))
          case _ =>
            (false, ErrorJudgment("InferFix", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferForallInstantiation = Rule {
    case g @ InferGoal(c, e @ Inst(t1, t2)) =>
      TypeChecker.debugs(g, "InferForallInstantiation")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case IntersectionType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, "Expecting an intersection type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer type for " + termOutput(t1))
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, _, ty),
            Cons(CheckJudgment(_, _, _, _), _)) =>

            dropRefinements(ty) match {
              case IntersectionType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() =>
                    (false, ErrorJudgment("InferForallInstantiation", c,
                      "Could not infer type for " + termOutput(e) + " with InferForallInstantiation: error in letIn(" +
                      x.toString + "," + termOutput(t2) + "," + typeOutput(ty) + ")"
                    ))
                  case Some(t) =>
                    (true, InferJudgment("InferForallInstantiation", c, e, t))
                }
              case _ => (false, ErrorJudgment("InferForallInstantiation", c,
                "Could not infer type for " + termOutput(e) + " with InferForallInstantiation: expecting an intersection type for " + 
                termOutput(t1) + ", found " + typeOutput(ty)))
            }

          case _ => (false, ErrorJudgment("InferForallInstantiation", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferApp = Rule {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.debugs(g, "InferApp")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, "Expecting a Pi type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
          ErrorGoal(c, anyToString(g1))
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, _, ty),
            Cons(CheckJudgment(_, _, _, _), _)) =>
            dropRefinements(ty) match {
              case PiType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() =>
                    (false, ErrorJudgment("InferApp", c,
                      "Could not infer type for " + termOutput(e) + " with InferApp: error in letIn(" +
                      x.toString + ", " + termOutput(t2) + ", " + typeOutput(ty) + ")"))
                  case Some(t) =>
                    (true, InferJudgment("InferApp", c, e, t))
                }
              case _ => (false, ErrorJudgment("InferApp", c,
                "Could not infer type for " + termOutput(e) + " with InferApp: expecting a Pi type for " +
                termOutput(t1) + ", found: " + typeOutput(ty)))
            }

          case _ =>
            (false, ErrorJudgment("InferApp", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val UnsafeIgnoreEquality = Rule {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug("In context:\n" + c.toString)
      TypeChecker.equalityDebug("Ignoring equality: " + anyToString(g))
      Some(List(), _ => (false, ErrorJudgment("UnsafeIgnoreEquality", c, bold("IGNORED") + anyToString(g))))
    case g =>
      None()
  }

  val CatchErrorGoal = Rule {
    case ErrorGoal(c, s) =>
      Some(List(), _ => (false, ErrorJudgment("CatchErrorGoal", c, s)))
    case g =>
      None()
  }

  val CatchEmptyGoal = Rule {
    case EmptyGoal(c) =>
      Some(List(), _ => (true, EmptyJudgment("CatchEmptyGoal", c)))
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
      TypeChecker.debugs(g, "CheckRefinement")
      val checkTy = CheckGoal(c.incrementLevel(), t, ty)
      val c1 = c.bind(id, ty).addEquality(Var(id), t)
      val checkRef = EqualityGoal(c1.incrementLevel(), b, BooleanLiteral(true))
      Some((
        List(_ => checkTy, _ => checkRef), {
          case Cons(CheckJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
            (true, CheckJudgment("CheckRefinement", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRefinement", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val CheckReflexive = Rule {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.debugs(g, "CheckReflexive")
      val gInfer = InferGoal(c.incrementLevel(), t)
      Some((List(_ => gInfer),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) if (dropRefinements(tpe) == ty) =>
            (true, CheckJudgment("CheckReflexive", c, t, ty))
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (false, ErrorJudgment("CheckReflexive", c,
              "Inferred type " + typeOutput(tpe) + " for " + termOutput(t) +
              ", expected: " + typeOutput(ty)))
          case _ =>
            (false, ErrorJudgment("CheckReflexive", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val FailRule = Rule { g => Some((List(), _ =>
    (false, ErrorJudgment("FailRule", g.c, "No more fuel or goal is not handled:\n" + anyToString(g)))
  ))}

  val InferPair = Rule {
    case g @ InferGoal(c, e @ Pair(t1, t2)) =>
      TypeChecker.debugs(g, "InferPair")
        val inferFirst = InferGoal(c.incrementLevel(), t1)
        val inferSecond = InferGoal(c.incrementLevel(), t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case Cons(InferJudgment(_, _, _, ty1), Cons(InferJudgment(_, _, _, ty2), _)) =>
            val inferredType = SigmaType(ty1, Bind(Identifier(0, "_X"), ty2))
            (true, InferJudgment("InferPair", c, e, inferredType))
          case _ =>
            (false, ErrorJudgment("InferPair", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferFirst = Rule {
    case g @ InferGoal(c, e @ First(t)) =>
      TypeChecker.debugs(g, "InferFirst")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, SigmaType(ty, _)), _) =>
            (true, InferJudgment("InferFirst", c, e, ty))
          case _ =>
            (false, ErrorJudgment("InferFirst", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferSecond = Rule {
    case g @ InferGoal(c, e @ Second(t)) =>
      TypeChecker.debugs(g, "InferSecond")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, SigmaType(_, Bind(x, ty))), _) =>
            TypeOperators.letIn(x, None(), First(t), ty) match {
                  case None() => (false, ErrorJudgment("InferSecond", c,
                    "Could not infer type for " + termOutput(e) + " with InferSecond: error in letIn(" + 
                    x.toString + ", " +
                    termOutput(First(t)) + ", " +
                    typeOutput(ty) + ")"))
                  case Some(t) => (true, InferJudgment("InferSecond", c, e, t))
                }
          case _ =>
            (false, ErrorJudgment("InferSecond", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferLeft = Rule {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.debugs(g, "InferLeft")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferLeft", c, e, SumType(tpe, BottomType)))
          case _ =>
            (false, ErrorJudgment("InferLeft", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferRight = Rule {
    case g @ InferGoal(c, e @ RightTree(t)) =>
      TypeChecker.debugs(g, "InferRight")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferRight", c, e, SumType(BottomType, tpe)))
          case _ =>
            (false, ErrorJudgment("InferRight", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckLeft = Rule {
    case g @ CheckGoal(c, e @ LeftTree(t), tpe @ SumType(ty, _)) =>
      TypeChecker.debugs(g, "CheckLeft")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckLeft", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLeft", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckRight = Rule {
    case g @ CheckGoal(c, e @ RightTree(t), tpe @ SumType(_, ty)) =>
      TypeChecker.debugs(g, "CheckRight")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckRight", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRight", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckLambda = Rule {
    case g @ CheckGoal(c, e @ Lambda(Some(ty1), Bind(id1, body)), tpe @ PiType(ty2, Bind(id2, ty))) if (ty1.isEqual(ty2)) =>
      TypeChecker.debugs(g, "CheckLambda")
      val (freshId, c1) = c.bindFresh(id1.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), body.replace(id1, Var(freshId)), ty.replace(id2, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckLambda", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLambda", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckPi = Rule {
    case g @ CheckGoal(c, t, tpe @ PiType(ty1, Bind(id,ty2))) =>
      TypeChecker.debugs(g, "CheckPi")
      val (freshId, c1) = c.bindFresh(id.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), App(t, Var(freshId)), ty2.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckPi", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckPi", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckIf = Rule {
    case g @ CheckGoal(c, e @ IfThenElse(tc, t1, t2), ty) =>
      TypeChecker.debugs(g, "CheckIf")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BooleanLiteral(true))
      val c2 = c0.addEquality(tc, BooleanLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val checkT1 = CheckGoal(c1, t1, ty)
      val checkT2 = CheckGoal(c2, t2, ty)
      Some((
        List(_ => checkCond, _ => checkT1, _ => checkT2),
        {
          case Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            _
          ))) =>
            (true, CheckJudgment("CheckIf", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckIf", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val CheckMatch = Rule {
    case g @ CheckGoal(c, e @ Match(t, t0, Bind(id, tn)), ty) =>
      TypeChecker.debugs(g, "CheckMatch")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val checkT0 = CheckGoal(c0, t0, ty)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val checkTn = CheckGoal(cn, tn, ty)
      Some((
        List(_ => checkN, _ => checkT0, _ => checkTn), {
          case Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _), _
          ))) =>
            (true, CheckJudgment("CheckMatch", c, e, ty))
          case _ => (false, ErrorJudgment("CheckMatch", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val CheckEitherMatch = Rule {
    case g @ CheckGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), tpe) =>
      TypeChecker.debugs(g, "CheckEitherMatch")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val fcheckT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, tpe)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) + ", found: " + typeOutput(ty))
          }
        case _ => ErrorGoal(c, "Could not infer a type for: " + termOutput(t))
      }
      val fcheckT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              CheckGoal(c2, t2, tpe)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) + ", found: " + typeOutput(ty))
          }
        case _ => ErrorGoal(c, "Could not infer a type for: " + termOutput(t))
      }
      Some((
        List(_ => inferScrutinee, fcheckT1, fcheckT2), {
          case Cons(InferJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _), _
          ))) =>
            (true, CheckJudgment("CheckEitherMatch", c, e, tpe))

          case _ => (false, ErrorJudgment("CheckEitherMatch", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val CheckPair = Rule {
    case g @ CheckGoal(c, e @ Pair(t1, t2), ty @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "CheckFirst")
      val letTy2 = TypeOperators.letIn(id, None(), t1, ty2)
      if (letTy2.isEmpty) None()
      else {
        val subgoal1 = CheckGoal(c.incrementLevel(), t1, ty1)
        val subgoal2 = CheckGoal(c.incrementLevel(), t2, letTy2.get)
        Some((List(_ => subgoal1, _ => subgoal2),
          {
            case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
              (true, CheckJudgment("CheckPair", c, e, ty))
            case _ =>
              (false, ErrorJudgment("CheckPair", c, anyToString(g)))
          }
        ))
      }
    case g =>
      None()
  }

  val CheckSigma = Rule {
    case g @ CheckGoal(c, t, tpe @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "CheckSigma")
        val checkFirst = CheckGoal(c.incrementLevel(), First(t), ty1)
        val c1 = c.bind(id, ty2).addEquality(Var(id), First(t)).incrementLevel
        val checkSecond = CheckGoal(c1, Second(t), ty2)
      Some((List(_ => checkFirst, _ => checkSecond),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckSigma", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckSigma", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckIntersection = Rule {
    case g @ CheckGoal(c, t, tpe @ IntersectionType(tyid, Bind(id, ty))) =>
      TypeChecker.debugs(g, "CheckIntersection")
      val (freshId, c1) = c.bindFresh(id.name, tyid)
      val subgoal = CheckGoal(c1.incrementLevel(), Inst(t, Var(freshId)), ty.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckIntersection", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckIntersection", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckLet = Rule {
    case g @ CheckGoal(c, e @ LetIn(None(), v, Bind(id, body)), ty) =>
      TypeChecker.debugs(g, "CheckLet")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, tyv), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            CheckGoal(c1, body, ty)
          case _ =>
            ErrorGoal(c, "Could not infer type for: " + termOutput(v))
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, anyToString(g)))
        }
      ))

    case g @ CheckGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body)), ty) =>
      TypeChecker.debugs(g, "CheckLet")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = CheckGoal(c1, body, ty)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, anyToString(g)))
        }
      ))

    case g =>
      None()
  }

  val InferFold = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ RecType(n, Bind(a, ty))), t)) =>
      TypeChecker.debugs(g, "InferFold")
      val checkN = CheckGoal(c.incrementLevel(), n, NatType)
      val c1 = c.addEquality(n, NatLiteral(0))
      val checkBase = CheckGoal(c1.incrementLevel(), t, TypeOperators.basetype(a, ty))
      val (id, c2) = c.bindFresh("_n", NatType)
      val n2 = Var(id)
      val c3 = c2.addEquality(
        n,
        Primitive(Plus, List(n2, NatLiteral(1)))
      )
      val nTy = RecType(n2, Bind(a, ty))
      val check = CheckGoal(c3.incrementLevel(), t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => checkN, _ => checkBase, _ => check),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _))) =>
            (true, InferJudgment("InferFold", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferFold", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckRecursive = Rule {
    case g @ CheckGoal(c, t, tpe @ RecType(n1, bind1)) =>
      TypeChecker.debugs(g, "CheckRecursive")
      val subgoal = InferGoal(c.incrementLevel(), t)
      val fEquality: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, ty2), _) =>
            dropRefinements(ty2) match {
              case tpe2 @ RecType(n2, bind2) if (Tree.areEqual(bind1, bind2)) => EqualityGoal(c.incrementLevel(), n1, n2)
              case _ => ErrorGoal(c,
                "Expecting type " + typeOutput(tpe) + " for " + termOutput(t) +
                ", found: " + typeOutput(ty2))
            }
          case _ =>
            ErrorGoal(c, anyToString(g))
        }
      Some((
        List(_ => subgoal, fEquality),
        {
          case Cons(InferJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
            (true, CheckJudgment("CheckRecursive", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRecursive", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val CheckTop1 = Rule {
    case g @ CheckGoal(c, t, TopType) if t.isValue =>
      TypeChecker.debugs(g, "CheckTop1")
      Some((List(), _ => (true, CheckJudgment("CheckTop1", c, t, TopType))))
    case g =>
      None()
  }

  val CheckTop2 = Rule {
    case g @ CheckGoal(c, t, TopType) =>
      TypeChecker.debugs(g, "CheckTop2")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckTop2", c, t, TopType))
          case _ =>
            (false, ErrorJudgment("CheckTop2", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferUnfold = Rule {
    case g @ InferGoal(c, e @ Unfold(t1, Bind(x, t2))) =>
      TypeChecker.debugs(g, "InferUnfold")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
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
            case _ => ErrorGoal(c,
              "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer a type for: " + termOutput(t1))
      }
      val fg3: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
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
            case _ => ErrorGoal(c,
              "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer a type for: " + termOutput(t1))
      }
      Some((
        List(_ => g1, fg2, fg3), {
          case Cons(InferJudgment(_, _, _, ty),
            Cons(InferJudgment(_, _, _, ty1),
            Cons(j3, _))) =>
            dropRefinements(ty) match {
              case IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty)))) =>
                // FIXME: check strict positive before generating goals
                if (TypeOperators.spos(a, ty)) (true, InferJudgment("InferUnfold", c, e, ty1))
                else (false, ErrorJudgment("InferUnfold", c,
                  "Could not infer type for " + termOutput(e) +
                  " with InferUnFold: " + a.toString + " does not appears strictly positively in " +
                  typeOutput(ty)))

              case RecType(n, Bind(x, ty)) =>
                j3 match {
                  case InferJudgment(_, _, _, ty2) =>
                    if (ty1.isEqual(ty2)) (true, InferJudgment("InferUnfold", c, e, ty1))
                    else {
                      (
                        false,
                        ErrorJudgment(
                          "InferUnfold",
                          c,
                          "Could not infer type for: " + termOutput(e) + " with InferUnfold: " +
                          typeOutput(ty1) + " is not equal to " + typeOutput(ty2)
                        )
                      )
                    }
                  case _ => (false, ErrorJudgment("InferUnfold", c, anyToString(g)))
                }
               case _ =>
                (false, ErrorJudgment("InferUnfold", c,
                  "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty)))
            }
          case _ =>
            (false, ErrorJudgment("InferUnfold", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val NewInferUnfoldPositive = Rule {
    case g @ InferGoal(c, e @ UnfoldPositive(t1, Bind(x, t2))) =>
      TypeChecker.debugs(g, "InferUnfoldPositive")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg3: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case RecType(n, Bind(a, ty)) =>
              val nTy = Tree.replace(a, RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty)), ty)
              val c2 = c.addEquality(
                t1,
                Fold(Some(RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty))), Var(x))
              ).bind(x, nTy)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c,
              "Expecting a rec type for: " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
          ErrorGoal(c, anyToString(g1))
      }
      Some((
        List(_ => g1, fg3), {
          case Cons(InferJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty2), _)) =>
            (true, InferJudgment("NewInferUnfoldPositive", c, e, ty2))
          case _ => (false, ErrorJudgment("NewInferUnfoldPositive", c, anyToString(g)))
        }
      ))

    case _ => None()
  }

  val InferTypeAbs = Rule {
    case g @ InferGoal(c, e @ Abs(Bind(a, t))) =>
      TypeChecker.debugs(g, "InferTypeAbs")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferTypeAbs", c, e, PolyForallType(Bind(a, tpe))))
          case _ =>
            (false, ErrorJudgment("InferTypeAbs", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val InferTypeApp = Rule {
    case g @ InferGoal(c, e @ TypeApp(t, ty)) =>
      TypeChecker.debugs(g, "InferTypeApp")
      val c1 = c.incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, PolyForallType(Bind(x, tpe))), _) =>
            (true, InferJudgment("InferTypeApp", c, e, tpe.replace(x, ty)))
          case Cons(InferJudgment(_, _, _, ty), _) =>
            (false, ErrorJudgment("InferTypeApp", c,
              "Expecting (polymorphic) forall type for: " + termOutput(t) +
              ", found: " + typeOutput(ty)))
          case _ =>
            (false, ErrorJudgment("InferTypeApp", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val CheckTypeAbs = Rule {
    case g @ CheckGoal(c, t, tpe @ PolyForallType(Bind(a, ty))) =>
      TypeChecker.debugs(g, "CheckTypeAbs")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = CheckGoal(c1, TypeApp(t, Var(a)), ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckTypeAbs", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckTypeAbs", c,  anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  def unfoldRefinementInContext(c: Context): Context = {
    val c1 = c.variables.foldLeft(c) { case (acc, x) =>
      c.getTypeOf(x) match {
        case Some(RefinementType(ty, Bind(y, t2))) =>
          val t2p = t2.replace(y, Var(x))
          c.copy(
            termVariables = c.termVariables.updated(x, ty)
          ).addEquality(t2p, BooleanLiteral(true))
        case _ => acc
      }
    }
    c1
  }

  val NewUnfoldRefinementInContext = Rule {
    case g @ EqualityGoal(c, t1, t2) if c.hasRefinementBound =>
      TypeChecker.debugs(g, "UnfoldRefinementInContext")
      val c1 = unfoldRefinementInContext(c)
      val subgoal = EqualityGoal(c1.incrementLevel(), t1, t2)
      Some((List(_ => subgoal),
        {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) =>
            (true, AreEqualJudgment("NewUnfoldRefinementInContext", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("NewUnfoldRefinementInContext", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }

  val NewNatEqualToEqual = Rule {
    case g @ EqualityGoal(c, Primitive(Eq, Cons(t1, Cons(t2, Nil()))), BooleanLiteral(true)) =>
      TypeChecker.debugs(g, "NewNatEqualToEqual")

      Some((List(
        _ => EqualityGoal(c.incrementLevel(), t1, t2),
        _ => CheckGoal(c.incrementLevel(), t1, NatType),
        _ => CheckGoal(c.incrementLevel(), t2, NatType)
        ),
        {
          case
            Cons(AreEqualJudgment(_, _, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _), _))) =>
            (true, AreEqualJudgment("NewNatEqualToEqual", c, Primitive(Eq, Cons(t1, Cons(t2, Nil()))), BooleanLiteral(true), ""))
          case _ =>
            (false, ErrorJudgment("NewNatEqualToEqual", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }


  val InferFoldGen = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty))))), t)) =>
      /* Fail if n != m */
      TypeChecker.debugs(g, "InferFoldGen")
      val nTy = IntersectionType(NatType, Bind(n, RecType(Var(n), Bind(a, ty))))
      val check = CheckGoal(c.incrementLevel(), t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => check),
        {
          case Cons(CheckJudgment(_, _, _, _), _) if TypeOperators.spos(a, ty) =>
            (true, InferJudgment("InferFoldGen", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferFoldGen", c, anyToString(g)))
        }
      ))
    case g =>
      None()
  }


  val NewEqualityInContext = Rule {
    case g @ EqualityGoal(c, t1, t2) if
      c.variables.exists(v =>
        c.termVariables.contains(v) && (
          c.termVariables(v) == EqualityType(t1,t2) ||
          c.termVariables(v) == EqualityType(t2,t1)
        )
      )
      =>
      TypeChecker.debugs(g, "EqualityInContext")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment("NewEqualityInContext", c, t1, t2, "By Assumption"))
        }
      ))
    case g =>
      None()
  }

  def findEquality(l: List[Identifier], termVariables: Map[Identifier, Tree], id: Identifier): Option[Tree] = l match {
    case Nil() => None()
    case Cons(v, vs) if termVariables.contains(v) => termVariables(v) match {
      case EqualityType(Var(id2), t) if id == id2 =>
        Some(t)
      case EqualityType(t, Var(id2)) if id == id2 && !t.isInstanceOf[Var] =>
        Some(t)
      case _ => findEquality(vs, termVariables, id)
    }
    case Cons(v, vs) => findEquality(vs, termVariables, id)
  }

  // TODO: move to Stainless library
  def collectFirst[A,B](l: List[A], f: A => Option[B]): Option[B] = l match {
    case Nil() => None()
    case Cons(x, xs) => f(x) orElse collectFirst(xs, f)
  }

  def mapFirst[A](l: List[A], f: A => Option[A]): Option[List[A]] = l match {
    case Nil() => None()
    case Cons(x, xs) =>
      f(x).map[List[A]](y => Cons(y, xs)) orElse
      mapFirst(xs, f).map[List[A]](ys => Cons(x, ys))
  }

  def mapFirstWithResult[A,B](l: List[A], f: A => Option[(A,B)]): Option[(List[A], B)] = l match {
    case Nil() => None()
    case Cons(x, xs) =>
      f(x).map[(List[A], B)] { case (y,b) => (Cons(y, xs), b) } orElse
      mapFirstWithResult(xs, f).map[(List[A], B)]{ case (ys,b) => (Cons(x, ys), b) }
  }

  // This function expand variables in a tree, but shouldn't go under lambdas
  // For a term t, it should hold that if expandVars(c, t) = Some(t'), then c ⊢ t ≡ t'
  // For a type ty, it should hold that if expandVars(c, ty) = Some(ty'), then
  // for all substitutions consistent with c, the denotations of ty and ty'
  // are the same.
  def expandVars(c: Context, t: Tree): Option[Tree] = t match {
    case Var(id) => findEquality(c.variables, c.termVariables, id)
    case Primitive(op, args) =>
      mapFirst(args, (arg: Tree) => expandVars(c, arg)).map(newArgs =>
        Primitive(op, newArgs)
      )
    case App(t1, t2) =>
      expandVars(c, t1).map[Tree](newT1 => App(newT1, t2)) orElse
      expandVars(c, t2).map[Tree](newT2 => App(t1, newT2))
    case EqualityType(t1, t2) =>
      expandVars(c, t1).map[Tree](newT1 => EqualityType(newT1, t2)) orElse
      expandVars(c, t2).map[Tree](newT2 => EqualityType(t1, newT2))
    case _ => None()
  }

  def expandVars(c: Context, l: List[Identifier]): Option[Context] = l match {
    case Nil() => None()
    case Cons(v, vs) if c.termVariables.contains(v) =>
      expandVars(c.copy(variables = l.tail), c.termVariables(v)).map(
        ty => c.copy(termVariables = c.termVariables.updated(v, ty))
      ) orElse expandVars(c, vs)
    case Cons(_, vs) => expandVars(c, vs)
  }

  def expandVars(c: Context): Option[Context] = expandVars(c, c.variables)

  def expandVars(g: Goal): Option[Goal] = g match {
    case InferGoal(c, t) =>
      expandVars(c).map(newC => InferGoal(newC, t): Goal) orElse
      expandVars(c, t).map(newT => InferGoal(c, newT): Goal)
    case CheckGoal(c, t, tp) =>
      expandVars(c).map(newC => CheckGoal(newC, t, tp): Goal) orElse
      expandVars(c, t).map(newT => CheckGoal(c, newT, tp): Goal) orElse
      expandVars(c, tp).map(newTp => CheckGoal(c, t, newTp): Goal)
    case EqualityGoal(c, t1, t2) =>
      expandVars(c).map(newC => EqualityGoal(newC, t1, t2): Goal) orElse
      expandVars(c, t1).map(newT1 => EqualityGoal(c, newT1, t2): Goal) orElse
      expandVars(c, t2).map(newT2 => EqualityGoal(c, t1, newT2): Goal)
    case SynthesisGoal(c, tp) =>
      expandVars(c).map(newC => SynthesisGoal(newC, tp): Goal) orElse
      expandVars(c, tp).map(newTp => SynthesisGoal(c, newTp): Goal)
    case _ => None()
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], g: Goal): Option[(Goal, T)] = g match {
    case InferGoal(c, t) =>
      lift(f, c, t).map { case (newT, a) => (InferGoal(c, newT): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case CheckGoal(c, t, tp) =>
      lift(f, c, t).map { case (newT, a) => (CheckGoal(c, newT, tp): Goal, a) } orElse
      lift(f, c, tp).map { case (newTp, a) => (CheckGoal(c, t, newTp): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case EqualityGoal(c, t1, t2) =>
      lift(f, c, t1).map { case (newT1, a) => (EqualityGoal(c, newT1, t2): Goal, a) } orElse
      lift(f, c, t2).map { case (newT2, a) => (EqualityGoal(c, t1, newT2): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case SynthesisGoal(c, tp) =>
      lift(f, c, tp).map { case (newTp, a) => (SynthesisGoal(c, newTp): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case _ => None()
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context, l: List[Identifier]): Option[(Context, T)] = {
    l match {
      case Nil() => None()
      case Cons(v, vs) if c.termVariables.contains(v) =>
        lift(f, c.copy(variables = vs), c.termVariables(v)).map {
          case (e, a) =>
            (c.copy(termVariables = c.termVariables.updated(v, e)), a)
        } orElse {
          lift(f, c, vs)
        }
      case Cons(v, vs) => lift(f, c, vs)
    }
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context): Option[(Context, T)] = {
    lift(f, c, c.variables)
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context, t: Tree): Option[(Tree, T)] = f(c, t) orElse {
    t match {
      case EqualityType(t1, t2) =>
        lift(f, c, t1).map { case (newT1, x) => (EqualityType(newT1, t2): Tree, x) } orElse
        lift(f, c, t2).map { case (newT2, x) => (EqualityType(t1, newT2): Tree, x) }
      case Primitive(op, args) =>
        mapFirstWithResult(args, (arg: Tree) => lift(f, c, arg)).map {
          case (newArgs, x) => (Primitive(op, newArgs), x)
        }
      case _ => None()
    }
  }

  val NewExpandVars = Rule {
    case g @ EqualityGoal(c, t1, t2) =>
      expandVars(g).map { sg =>
        TypeChecker.debugs(g, "NewExpandVars")
        (List(_ => sg), {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) =>
            (true, AreEqualJudgment("NewExpandVars", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("NewExpandVars", c, anyToString(g)))
        })
      }
    case g =>
      None()
  }

  def optionToList[T](opt: Option[T]): List[T] = opt match {
    case None() => Nil()
    case Some(v) => List(v)
  }

  def inlineApplicationsTop(c: Context, e: Tree): Option[(Tree, (Goal, Identifier))] = {
    e match {
      case App(Lambda(tp, Bind(id, body)), t) =>
        val subgoal = if (tp.isEmpty) InferGoal(c, t) else CheckGoal(c, t, tp.get)
        val (freshId, _) = c.getFresh(id.name)
        Some(body.replace(id, Var(freshId)), (subgoal, freshId))

      case LetIn(tp, value, body) => inlineApplicationsTop(c, App(Lambda(tp, body), value))

      case _ => None()
    }
  }

  val NewInlineApplications = Rule {
    case g @ EqualityGoal(c, t1, t2) =>

      val res = lift((c: Context, t: Tree) => inlineApplicationsTop(c, t), g)

      res.map {
        case (g2, (subgoal, freshId)) =>
          def newGoal(prev: List[Judgment]): Goal = prev match {
            case Cons(InferJudgment(_, _, t, tp), Nil()) =>
              val c1 = g2.c.incrementLevel().bind(freshId, tp)
              val c2 = c1.addEquality(Var(freshId), t)
              g2.updateContext(c2)
            case Cons(CheckJudgment(_, _, t, tp), Nil()) =>
              val c1 = g2.c.incrementLevel().bind(freshId, tp)
              val c2 = c1.addEquality(Var(freshId), t)
              g2.updateContext(c2)
            case _ => ErrorGoal(c, "Attempted to inline an application or a val, but could not type check the argument.")
          }
          (List(_ => subgoal, newGoal), {
            case Cons(_, Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
              (true, AreEqualJudgment("NewInlineApplications", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("NewInlineApplications", c, anyToString(g)))
          })
      }

    case g =>
      None()
  }

  def topIf(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case IfThenElse(tc, tt, tf) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, BooleanLiteral(true))
        val c2 = c0.addEquality(tc, BooleanLiteral(false))
        val checkC = CheckGoal(c0, tc, BoolType)
        val equalT1 = EqualityGoal(c1, tt, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => checkC, _ => equalT1, _ => equalT2),
          {
            case Cons(CheckJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _))) =>
              (true, AreEqualJudgment("NewTopIf", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("NewTopIf", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None()
    }
  }

  val NewTopIf = Rule {
    case g @ EqualityGoal(c, t1 @ IfThenElse(tc, tt, tf), t2) =>
      TypeChecker.debugs(g, "NewTopIf")
      topIf(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ IfThenElse(tc, tt, tf)) =>
      TypeChecker.debugs(g, "NewTopIf")
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
            case Cons(CheckJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _))) =>
              (true, AreEqualJudgment("NewTopMatch", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("NewTopMatch", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None()
    }
  }

  val NewTopMatch = Rule {
    case g @ EqualityGoal(c, t1 @ Match(tc, tt, tf), t2) =>
      TypeChecker.debugs(g, "NewTopMath")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ Match(tc, tt, tf)) =>
      TypeChecker.debugs(g, "NewTopMatch")
      topEitherMatch(c, t2, t1)
    case g =>
      None()
  }


  // FIXME: infer the type of `tc`
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
            case Cons(AreEqualJudgment(_, _, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
              (true, AreEqualJudgment("NewTopEitherMatch", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("NewTopEitherMatch", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None()
    }
  }

  val NewTopEitherMatch = Rule {
    case g @ EqualityGoal(c, t1 @ EitherMatch(tc, tt, tf), t2) =>
      TypeChecker.debugs(g, "NewTopEitherMath")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ EitherMatch(tc, tt, tf)) =>
      TypeChecker.debugs(g, "NewTopEitherMatch")
      topEitherMatch(c, t2, t1)
    case g =>
      None()
  }

  val InferTypeDefinition = Rule {
    case g @ InferGoal(c, e @ TypeDefinition(ty, Bind(id, t))) =>
      TypeChecker.debugs(g, "InferTypeDefinition")
      // TypeChecker.debugs(g, "InferTypeDefinition")
      val subgoal = InferGoal(c, t.replace(id, ty))
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferTypeDefinition", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferTypeDefinition", c, anyToString(g)))
        }
      ))
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
      case BooleanLiteral(_) => true
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

  @extern
  def z3Encode(z3: Z3Context, solver: Z3Solver, variables: Map[Identifier, Z3AST], t: Tree): Z3AST = {
    t match {
      case Var(id) if variables.contains(id) => variables(id)
      case NatLiteral(n) => z3.mkInt(bigIntToInt(n), z3.mkIntSort())
      case BooleanLiteral(true) => z3.mkTrue()
      case BooleanLiteral(false) => z3.mkFalse()
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

  @extern
  val NewZ3ArithmeticSolver: Rule = Rule {
    case g @ EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, Cons(t1, Cons(t2, Nil())))) =>
      TypeChecker.debugs(g, "Z3ArithmeticSolver")
      TypeChecker.z3Debug("Current goal:\n" + g)
      TypeChecker.z3Debug("Current context:\n" + c)
      TypeChecker.z3Debug("\nInvoking Z3\n")

      val factory = Solver.getFactory
      val z3 = factory.getContext
      val solver = z3.mkSolver
      val i = z3.mkIntSort

      val z3Variables =
        ListOps.toMap(c.variables.filter(v => dropRefinements(c.termVariables(v)) == NatType).map {
          id => id -> z3.mkConst(z3.mkStringSymbol(id.toString), i)
        })

      c.variables.map { v =>
        c.termVariables(v) match {
          case EqualityType(h1, h2) if isNatPredicate(c.termVariables, Primitive(Eq, Cons(h1, Cons(h2, Nil())))) =>
            solver.assertCnstr(z3Encode(z3, solver, z3Variables, Primitive(Eq, Cons(h1, Cons(h2, Nil())))))
          case _ => ()
        }
      }

      val b = z3Encode(z3, solver, z3Variables, Primitive(Eq, Cons(t1, Cons(t2, Nil()))))
      solver.assertCnstr(z3.mkNot(b))

      c.variables.filter(c.termVariables(_) == NatType).map { id =>
        val v = z3.mkConst(z3.mkStringSymbol(id.toString), i)
        solver.assertCnstr(z3.mkGE(v, z3.mkInt(0, i)))
      }

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
        case scala.None =>
          None()
          // Some((List(), _ =>
          // (false, ErrorJudgment("NewZ3ArithmeticSolver", c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)}: Failure in Z3."))))
        case scala.Some(true) =>
          None()
          // Some((List(), _ =>
          // (false, ErrorJudgment("NewZ3ArithmeticSolver", c, s"Could not check equality between ${termOutput(t1)} and ${termOutput(t2)}: Z3 found a counter-example: $modelString."))))
        case scala.Some(false) => Some((List(), _ =>
          (true, AreEqualJudgment("NewZ3ArithmeticSolver", c, t1, t2, "Validated by Z3"))))
      }

    case g =>
      None()
  }

  val NewReflexivity = Rule {
    case g @ EqualityGoal(c, t1, t2) if t1.isEqual(t2) =>
      TypeChecker.debugs(g, "NewReflexivity")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment("NewReflexivity", c, t1, t2, "By Reflexivity"))
        }
      ))
    case g =>
      None()
  }

  val NewSynthesisUnit = Rule {
    case g @ SynthesisGoal(c, UnitType) =>
      Some((List(), _ => (true, SynthesisJudgment("NewSynthesisUnit", c, UnitType, UnitLiteral))))
    case g =>
      None()
  }

  val NewSynthesisBool = Rule {
    case g @ SynthesisGoal(c, BoolType) =>
      Some((List(), _ => (true, SynthesisJudgment("NewSynthesisBool", c, BoolType, BooleanLiteral(true)))))
    case g =>
      None()
  }

  val NewSynthesisNat = Rule {
    case g @ SynthesisGoal(c, NatType) =>
      Some((List(), _ => (true, SynthesisJudgment("NewSynthesisNat", c, NatType, NatLiteral(0)))))
    case g =>
      None()
  }

  val NewSynthesisVar = Rule {
    case g @ SynthesisGoal(c, tp) =>
      c.getVarOfType(tp).map(v =>
        (List(), _ => (true, SynthesisJudgment("NewSynthesisVar", c, NatType, Var(v))))
      )
    case g =>
      None()
  }

  val NewSynthesisPi = Rule {
    case g @ SynthesisGoal(c, tp @ PiType(tyX, Bind(x, ty))) =>
      val c1 = c.bind(x, tyX).incrementLevel
      val gb = SynthesisGoal(c, ty)
      Some((
        List(_ => gb),
        {
          case Cons(SynthesisJudgment(_, _, _, t), _) =>
            (true, SynthesisJudgment("NewSynthesisPi", c, tp, Lambda(Some(tyX), Bind(x, t))))
          case _ =>
            (false, ErrorJudgment("NewSynthesisPi", c, anyToString(g)))
        }
      ))
    case _ => None()
  }

  val NewSynthesisSigma = Rule {
    case g @ SynthesisGoal(c, tp @ SigmaType(ty1, Bind(id, ty2))) =>
      val g1 = SynthesisGoal(c.incrementLevel(), ty1)
      val fg2: List[Judgment] => Goal = {
        case Cons(SynthesisJudgment(_, _, _, t1), _) =>
          val c1 = c.incrementLevel.bind(id, t1)
          SynthesisGoal(c1, ty2)
        case _ =>
          ErrorGoal(c, anyToString(g1))
      }
      Some((
        List(_ => g1, fg2),
        {
          case Cons(SynthesisJudgment(_, _, _, t1), Cons(SynthesisJudgment(_, _, _, t2), _)) =>
            (true, SynthesisJudgment("NewSynthesisSigma", c, tp, Pair(t1, t2)))
          case _ =>
            (false, ErrorJudgment("NewSynthesisSigma", c,  anyToString(g)))
        }
      ))
    case _ => None()
  }

  val NewSynthesisSum = Rule {
    case g @ SynthesisGoal(c, tp @ SumType(ty1, ty2)) =>
      val g1 = SynthesisGoal(c.incrementLevel(), ty1)
      val g2 = SynthesisGoal(c.incrementLevel(), ty1)
      Some((
        List(_ => g1, _ => g2),
        {
          case Cons(SynthesisJudgment(_, _, _, t1), _) =>
            (true, SynthesisJudgment("NewSynthesisSum", c, tp, LeftTree(t1)))
          case Cons(_, Cons(SynthesisJudgment(_, _, _, t2), _)) =>
            (true, SynthesisJudgment("NewSynthesisSum", c, tp, RightTree(t2)))
          case _ =>
            (false, ErrorJudgment("NewSynthesisSum", c, anyToString(g)))
        }
      ))
    case _ => None()
  }


}


object TypeChecker {
  import Rule._

  val tactic = (
    CheckBool.t ||
    CheckNat.t ||
    CheckUnit.t ||
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
    InferErasableLambda.t ||
    InferIf.t ||
    InferBinaryPrimitive.t ||
    InferUnaryPrimitive.t ||
    InferMatch.t ||
    InferEitherMatch.t ||
    InferFix.t ||
    InferTypeAbs.t ||
    InferTypeApp.t ||
    InferForallInstantiation.t ||
    InferFold.t ||
    InferUnfold.t || NewInferUnfoldPositive.t ||
    InferFoldGen.t ||
    InferTypeDefinition.t ||
    NewZ3ArithmeticSolver.t ||
    NewExpandVars.t ||
    NewTopIf.t ||
    NewTopMatch.t ||
    NewReflexivity.t ||
    NewEqualityInContext.t ||
    NewNatEqualToEqual.t ||
    NewUnfoldRefinementInContext.t ||
    NewInlineApplications.t ||
    UnsafeIgnoreEquality.t ||
    CatchErrorGoal.t ||
    CatchEmptyGoal.t ||
    FailRule.t
  ).repeat(1000000000)

  val tdebug = false
  val edebug = false
  val zdebug = false
  val ndebug = false

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context.empty(max), t)
    tactic.apply(g, sg => None())
  }

  @extern
  def debugs(g: Goal, ruleName: String) = {
    TypeChecker.ruleNameDebug(s"${"   " * g.c.level}$ruleName")
    TypeChecker.typeCheckDebug(s"${"   " * g.c.level}Current goal ${g} $ruleName : ${replaceAll(g.c.toString, "\n", s"\n${"   " * g.c.level}")}\n")
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
