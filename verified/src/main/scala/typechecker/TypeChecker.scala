package typechecker

import _root_.trees._
import _root_.solver._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import z3.scala._

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

  def bind(i: Identifier, t: Tree) = {
    if (variables.contains(i)) throw new java.lang.Exception(s"Already bound ${i}")
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

  def containsVarOfType(tp: Tree): Boolean = variables.exists(termVariables(_) == tp)

  def getVarOfType(tp: Tree): Option[Identifier] = variables.find(termVariables(_) == tp)

  override def toString: String = {
    "Term variables:\n" ++
    variables.foldLeft("") {
      case (acc, id) => acc + s"${id}: ${termVariables(id)}\n"
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

  def replace(id: Identifier, t: Tree): Context = {
    copy(
      termVariables = variables.foldLeft(Map[Identifier, Tree]()) {
        case (m, termId) => m.updated(termId, Tree.replace(id, t, termVariables(termId)))
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
  override def toString: String = {
    s"Inferring $t"
  }

  def replace(id: Identifier, t1: Tree): Goal = {
    InferGoal(c.replace(id, t1), t.replace(id, t1))
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal {
  override def toString: String = {
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
  override def toString: String = {
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

  override def toString: String = {
    s"Error Goal: ${s}"
  }

  def replace(id: Identifier, t: Tree): Goal = {
    ErrorGoal(c.replace(id, t), s)
  }

  def updateContext(newC: Context): Goal = copy(c = newC)
}

case class EmptyGoal(c: Context) extends Goal {

  override def toString: String = {
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
                    case (subSuccess: Boolean, subTree: NodeTree[Judgment]) =>
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

  private def termOutput(t: Tree): String =
    Derivation.termColor(Derivation.shortString(t.toString))

  private def typeOutput(t: Tree): String =
    Derivation.typeColor(Derivation.shortString(t.toString))

  private def bold(s: String): String = Derivation.bold(s)

  val InferBool = Rule {
    case g @ InferGoal(c, BooleanLiteral(b)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferBool")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferBool : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((
        List(),
        _ => (true, InferJudgment("InferBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None()
  }

  val CheckBool = Rule {
    case g @ CheckGoal(c, BooleanLiteral(b), BoolType) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckBool")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckBool : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((
        List(),
        _ => (true, CheckJudgment("CheckBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None()
  }

  val InferNat = Rule {
    case g @ InferGoal(c, NatLiteral(n)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferNat")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferNat : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment("InferNat", c, NatLiteral(n), NatType))))
    case g =>
      None()
  }

  val CheckNat = Rule {
    case g @ CheckGoal(c, NatLiteral(n), NatType) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckNat")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckNat : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment("CheckNat", c, NatLiteral(n), NatType))))
    case g =>
      None()
  }

  val InferUnit = Rule {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferUnit")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnit : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, InferJudgment("InferUnit", c, UnitLiteral, UnitType))))
    case g =>
      None()
  }

  val CheckUnit = Rule {
    case g @ CheckGoal(c, UnitLiteral, UnitType) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckUnit")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckUnit : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment("CheckUnit", c, UnitLiteral, UnitType))))
    case g =>
      None()
  }

  val InferVar = Rule {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferVar")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferVar : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None() => (false, ErrorJudgment("InferVar", c, s"$id is not in context"))
          case Some(tpe) => (true, InferJudgment("InferVar", c, Var(id), tpe))
        }
      ))

    case g =>
      None()
  }

  val CheckVar = Rule {
    case g @ CheckGoal(c, Var(id), ty) if c.termVariables.getOrElse(id, UnitLiteral).areEqual(ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckVar")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckVar : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment("CheckVar", c, Var(id), ty))))
    case g =>
      None()
  }

  val InferError = Rule {
    case g @ InferGoal(c, e @ Error(_, Some(tp))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferError")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferError : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val errorGoal = EqualityGoal(c.incrementLevel(), BooleanLiteral(false), BooleanLiteral(true))
      Some((List(_ => errorGoal),
        {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) => (true, InferJudgment("InferError", c, e, tp))
          case _ => (false, ErrorJudgment("InferError", c, s"Could not infer ${typeOutput(tp)} for ${termOutput(e)} with InferError."))
        }
      ))

    case g =>
      None()
  }

  val InferLet = Rule {
    case g @ InferGoal(c, e @ LetIn(None(), v, Bind(id, body))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferLet")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, tyv), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c, s"Could not infer type for ${termOutput(v)}, so we didn't type check the rest.")
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(InferJudgment(_, _, _, tyb), _)) =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, g.toString))
        }
      ))

    case g @ InferGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferLet")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(InferJudgment(_, _, _, tyb), _)) =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, g.toString))
        }
      ))

    case g =>
      None()
  }

  val InferLambda = Rule {
    case g @ InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferLambda")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            (false, ErrorJudgment("InferLambda", c, g.toString))
        }
      ))

    case g =>
      None()
  }

  val InferErasableLambda = Rule {
    case g @ InferGoal(c, e @ ErasableLambda(ty1, Bind(id, body))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferErasableLambda")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferErasableLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")

      val erasedBody = body.erase

      if (id.isFreeIn(erasedBody))
        throw new java.lang.Exception(
          s"Could not infer a type for:\n$e\nwith InferFix: $id appears free in the erased term:\n$erasedBody"
        )

      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case Cons(InferJudgment(_, _, _, tyb), _) =>
            (true, InferJudgment("InferErasableLambda", c, e, IntersectionType(ty1, Bind(id, tyb))))
          case _ =>
            (false, ErrorJudgment("InferErasableLambda", c, g.toString))
        }
      ))

    case g =>
      None()
  }

  val InferIf = Rule {
    case g @ InferGoal(c, e @ IfThenElse(tc, t1, t2)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferIf")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
                  s"Could not infer type for ${termOutput(e)} with InferIf: cannot unify ${typeOutput(ty1)}  and ${typeOutput(ty2)}"
                )
              )
              case Some(ty) =>
                (true, InferJudgment("InferIf", c, e, ty))
            }

          case _ =>
            (false, ErrorJudgment("InferIf", c, g.toString))
        }
      ))

    case g =>
      None()
  }

  val InferBinaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Cons(n2, Nil())))) if op.isBinOp =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferBinaryPrimitive")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferBinaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            (false, ErrorJudgment("InferBinaryPrimitive", c, g.toString))
        }
      ))

    case _ => None()
  }

  val InferUnaryPrimitive = Rule {
    case g @ InferGoal(c, e @ Primitive(op, Cons(n1, Nil()))) if op.isUnOp =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferUnaryPrimitive")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnaryPrimitive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel(), n1, opType)
      Some((
        List(_ => checkN1),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, InferJudgment("InferUnaryPrimitive", c, e, op.returnedType))
          case _ =>
            (false, ErrorJudgment("InferUnaryPrimitive", c, g.toString))
        }
      ))

    case _ => None()
  }

  val InferMatch = Rule {
    case g @ InferGoal(c, e @ Match(t, t0, Bind(id, tn))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferMatch: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
                  s"Cannot unify types ${typeOutput(ty0)} and ${typeOutput(tyn)}. $g"
                )
              )
              case Some(ty) => (true, InferJudgment("InferMatch", c, e, ty))
            }

          case _ =>
            (false, ErrorJudgment("InferMatch", c, g.toString))
        }
      ))

    case _ => None()
  }

  val InferEitherMatch = Rule {
    case g @ InferGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferEitherMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)

      val finferT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)}, then body of either_match is not typechecked.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}, then body of either_match is not typechecked.")
      }

      val finferT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)} then body of either_match is not typechecked. $g")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)} then body of either_match is not typechecked.")
      }

      Some((
        List(_ => inferScrutinee, finferT1, finferT2), {
          case Cons(InferJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty1),
            Cons(InferJudgment(_, _, _, ty2), _))) =>
              TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
                case None() => (false, ErrorJudgment("InferEitherMatch", c, s"Could not unify the types ${typeOutput(ty1)} and ${typeOutput(ty2)}. $g"))
                case Some(ty) => (true, InferJudgment("InferEitherMatch", c, e, ty))
              }

          case _ => (false, ErrorJudgment("InferEitherMatch", c, s"Could not infer a type for ${termOutput(e)} with InferEitherMatch."))
        }
      ))

    case _ => None()
  }

  val InferFix = Rule {
    case g @ InferGoal(c, e @ Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferFix")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFix : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")

      if (n1.isFreeIn(t.erase))
        throw new java.lang.Exception(
          s"Could not infer a type for:\n$e\nwith InferFix: $n1 appears free in the erased term:\n${t.erase}"
        )

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
            (false, ErrorJudgment("InferFix", c, g.toString))
        }
      ))

    case _ => None()
  }

  val InferForallInstantiation = Rule {
    case g @ InferGoal(c, e @ Inst(t1, t2)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferForallInstantiation")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferForallInstantiation : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case IntersectionType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting an intersection type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer type for ${termOutput(t1)}.")
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
                      s"Could not infer type for ${termOutput(e)} with InferForallInstantiation: error in letIn($x, ${termOutput(t2)}, ${typeOutput(ty)})."))
                  case Some(t) =>
                    (true, InferJudgment("InferForallInstantiation", c, e, t))
                }
              case _ => (false, ErrorJudgment("InferForallInstantiation", c,
                s"Could not infer type for ${termOutput(e)} with InferForallInstantiation: expecting an intersection type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }

          case _ => (false, ErrorJudgment("InferForallInstantiation", c, s"Could not infer type for ${termOutput(e)} with InferForallInstantiation."))
        }
      ))

    case _ => None()
  }

  val InferApp = Rule {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferApp")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferApp : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, s"Expecting a pi type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg2), {
          case Cons(InferJudgment(_, _, _, ty),
            Cons(CheckJudgment(_, _, _, _), _)) =>
            dropRefinements(ty) match {
              case PiType(_, Bind(x, ty)) =>
                TypeOperators.letIn(x, None(), t2, ty) match {
                  case None() => (false, ErrorJudgment("InferApp", c, s"Could not infer type for ${termOutput(e)} with InferApp: error in letIn($x, ${termOutput(t2)}, ${typeOutput(ty)})."))
                  case Some(t) =>
                    (true, InferJudgment("InferApp", c, e, t))
                }
              case _ => (false, ErrorJudgment("InferApp", c,
                s"Could not infer type for ${termOutput(e)} with InferApp: expecting a pi type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }

          case _ =>
            (false, ErrorJudgment("InferApp", c, g.toString))
        }
      ))

    case _ => None()
  }

  val UnsafeIgnoreEquality = Rule {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug(s"Context:\n${c}\n")
      TypeChecker.equalityDebug(s"Ignoring equality ${t1} = ${t2}.\n\n")
      Some(List(), _ => (false, ErrorJudgment("UnsafeIgnoreEquality", c, s"Equality between ${termOutput(t1)} and ${termOutput(t2)} ${bold("IGNORED")}.")))
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
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckRefinement")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRefinement : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val checkTy = CheckGoal(c.incrementLevel(), t, ty)
      val c1 = c.bind(id, ty).addEquality(Var(id), t)
      val checkRef = EqualityGoal(c1.incrementLevel(), b, BooleanLiteral(true))
      Some((
        List(_ => checkTy, _ => checkRef), {
          case Cons(CheckJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
            (true, CheckJudgment("CheckRefinement", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRefinement", c, g.toString))
        }
      ))

    case _ => None()
  }

  val CheckReflexive = Rule {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckReflexive")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckReflexive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gInfer = InferGoal(c.incrementLevel(), t)
      Some((List(_ => gInfer),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) if (dropRefinements(tpe) == ty) =>
            (true, CheckJudgment("CheckReflexive", c, t, ty))
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (false, ErrorJudgment("CheckReflexive", c, s"Inferred type ${typeOutput(tpe)} for ${termOutput(t)}, expected: ${typeOutput(ty)}."))
          case _ =>
            (false, ErrorJudgment("CheckReflexive", c, g.toString))
        }
      ))
    case g =>
      None()
  }

  val FailRule = Rule { g => Some((List(), _ =>
    (false, ErrorJudgment("FailRule", g.c, s"No more fuel or goal is not handled:\n$g")))) }

  val InferPair = Rule {
    case g @ InferGoal(c, e @ Pair(t1, t2)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferPair")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferPair : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val inferFirst = InferGoal(c.incrementLevel(), t1)
        val inferSecond = InferGoal(c.incrementLevel(), t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case Cons(InferJudgment(_, _, _, ty1), Cons(InferJudgment(_, _, _, ty2), _)) =>
            val inferredType = SigmaType(ty1, Bind(Identifier(0, "X"), ty2))
            (true, InferJudgment("InferPair", c, e, inferredType))
          case _ =>
            (false, ErrorJudgment("InferPair", c, s"Could not infer type for ${termOutput(e)} with InferPair."))
        }
      ))
    case g =>
      None()
  }

  val InferFirst = Rule {
    case g @ InferGoal(c, e @ First(t)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferFirst")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFirst : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, SigmaType(ty, _)), _) =>
            (true, InferJudgment("InferFirst", c, e, ty))
          case _ =>
            (false, ErrorJudgment("InferFirst", c, s"Could not infer type for ${termOutput(e)} with InferFirst."))
        }
      ))
    case g =>
      None()
  }

  val InferSecond = Rule {
    case g @ InferGoal(c, e @ Second(t)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferSecond")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferSecond : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, SigmaType(_, Bind(x, ty))), _) =>
            TypeOperators.letIn(x, None(), First(t), ty) match {
                  case None() => (false, ErrorJudgment("InferSecond", c,
                    s"Could not infer type for ${termOutput(e)} with InferSecond: error in letIn($x, ${termOutput(First(t))}, ${typeOutput(ty)})"))
                  case Some(t) => (true, InferJudgment("InferSecond", c, e, t))
                }
          case _ =>
            (false, ErrorJudgment("InferSecond", c, s"Could not infer type for ${termOutput(e)} with InferSecond."))
        }
      ))
    case g =>
      None()
  }

  val InferLeft = Rule {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferLeft")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferLeft", c, e, SumType(tpe, BottomType)))
          case _ =>
            (false, ErrorJudgment("InferLeft", c, s"Could not infer type for ${termOutput(e)} with InferLeft."))
        }
      ))
    case g =>
      None()
  }

  val InferRight = Rule {
    case g @ InferGoal(c, e @ RightTree(t)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferRight")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferRight", c, e, SumType(BottomType, tpe)))
          case _ =>
            (false, ErrorJudgment("InferRight", c, s"Could not infer type for ${termOutput(e)} with InferRight."))
        }
      ))
    case g =>
      None()
  }

  val CheckLeft = Rule {
    case g @ CheckGoal(c, e @ LeftTree(t), tpe @ SumType(ty, _)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckLeft")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLeft : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckLeft", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLeft", c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckLeft."))
        }
      ))
    case g =>
      None()
  }

  val CheckRight = Rule {
    case g @ CheckGoal(c, e @ RightTree(t), tpe @ SumType(_, ty)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckRight")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRight : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckRight", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRight", c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckRight."))
        }
      ))
    case g =>
      None()
  }

  val CheckLambda = Rule {
    case g @ CheckGoal(c, e @ Lambda(Some(ty1), Bind(id1, body)), tpe @ PiType(ty2, Bind(id2, ty))) if (ty1.areEqual(ty2)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckLambda")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLambda : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id1.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), body.replace(id1, Var(freshId)), ty.replace(id2, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckLambda", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLambda", c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckLambda."))
        }
      ))
    case g =>
      None()
  }

  val CheckPi = Rule {
    case g @ CheckGoal(c, e @ t, tpe @ PiType(ty1, Bind(id,ty2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckPi")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckPi : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), App(t, Var(freshId)), ty2.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckPi", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckPi", c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckPi."))
        }
      ))
    case g =>
      None()
  }

  val CheckIf = Rule {
    case g @ CheckGoal(c, e @ IfThenElse(tc, t1, t2), ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckIf")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            (false, ErrorJudgment("CheckIf", c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckIf."))
        }
      ))

    case g =>
      None()
  }

  val CheckMatch = Rule {
    case g @ CheckGoal(c, e @ Match(t, t0, Bind(id, tn)), ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckkMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckkMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
          case _ => (false, ErrorJudgment("CheckMatch", c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckMatch."))
        }
      ))

    case _ => None()
  }

  val CheckEitherMatch = Rule {
    case g @ CheckGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), tpe) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckEitherMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val fcheckT1: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, tpe)
            case _ => ErrorGoal(c, s"Expecting a sum type for ${termOutput(t)}, found ${typeOutput(ty)}.")
          }
        case _ => ErrorGoal(c, s"Could not infer a type for ${termOutput(t)}.")
      }
      val fcheckT2: List[Judgment] => Goal = {
        case Cons(InferJudgment(_, _, _, ty), _) =>
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
          case Cons(InferJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _),
            Cons(CheckJudgment(_, _, _, _), _
          ))) =>
            (true, CheckJudgment("CheckEitherMatch", c, e, tpe))

          case _ => (false, ErrorJudgment("CheckEitherMatch", c, s"Could not check ${termOutput(e)} has type ${typeOutput(tpe)} with CheckEitherMatch."))
        }
      ))

    case _ => None()
  }

  val CheckPair = Rule {
    case g @ CheckGoal(c, e @ Pair(t1, t2), ty @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckFirst")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckFirst : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal1 = CheckGoal(c.incrementLevel(), t1, ty1)
      val subgoal2 = CheckGoal(c.incrementLevel(), t2, TypeOperators.letIn(id, None(), t1, ty2).get)
      Some((List(_ => subgoal1, _ => subgoal2),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckPair", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckPair", c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckPair."))
        }
      ))
    case g =>
      None()
  }

  val CheckSigma = Rule {
    case g @ CheckGoal(c, t, tpe @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckSigma")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckSigma : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        val checkFirst = CheckGoal(c.incrementLevel(), First(t), ty1)
        val c1 = c.bind(id, ty2).addEquality(Var(id), First(t)).incrementLevel
        val checkSecond = CheckGoal(c1, Second(t), ty2)
      Some((List(_ => checkFirst, _ => checkSecond),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckSigma", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckSigma", c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckSigma."))
        }
      ))
    case g =>
      None()
  }

  val CheckIntersection = Rule {
    case g @ CheckGoal(c, t, tpe @ IntersectionType(tyid, Bind(id, ty))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckIntersection")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckIntersection : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val (freshId, c1) = c.bindFresh(id.name, tyid)
      val subgoal = CheckGoal(c1.incrementLevel(), Inst(t, Var(freshId)), ty.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckIntersection", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckIntersection", c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckIntersection."))
        }
      ))
    case g =>
      None()
  }

  val CheckLet = Rule {
    case g @ CheckGoal(c, e @ LetIn(None(), v, Bind(id, body)), ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckLet")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, tyv), _) =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            CheckGoal(c1, body, ty)
          case _ =>
            ErrorGoal(c, s"Could not infer type for ${termOutput(v)}")
        }
      Some((
        List(_ => gv, fgb),
        {
          case Cons(_, Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckLet."))
        }
      ))

    case g @ CheckGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body)), ty) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckLet")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckLet : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = CheckGoal(c1, body, ty)
      Some((
        List(_ => gv, _ => gb),
        {
          case Cons(CheckJudgment(_, _, _, _), Cons(CheckJudgment(_, _, _, _), _)) =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, s"Could not check ${termOutput(e)} has type ${typeOutput(ty)} with CheckLet."))
        }
      ))

    case g =>
      None()
  }

  val InferFold = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ RecType(n, Bind(a, ty))), t)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferFold")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFold : ${g.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            (false, ErrorJudgment("InferFold", c, s"Could not infer type for ${termOutput(e)} with InferFold."))
        }
      ))
    case g =>
      None()
  }

  val CheckRecursive = Rule {
    case g @ CheckGoal(c, t, tpe @ RecType(n1, bind1)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckRecursive")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckRecursive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      val fEquality: List[Judgment] => Goal =
        {
          case Cons(InferJudgment(_, _, _, ty2), _) =>
            dropRefinements(ty2) match {
              case tpe2 @ RecType(n2, bind2) if (Tree.areEqual(bind1, bind2)) => EqualityGoal(c.incrementLevel(), n1, n2)
              case _ => ErrorGoal(c, s"Expecting type ${typeOutput(tpe)} for ${termOutput(t)}, found ${typeOutput(ty2)}.")
            }
          case _ =>
            ErrorGoal(c, g.toString)
        }
      Some((
        List(_ => subgoal, fEquality),
        {
          case Cons(InferJudgment(_, _, _, _), Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
            (true, CheckJudgment("CheckRecursive", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRecursive", c, g.toString))
        }
      ))

    case _ => None()
  }

  val CheckTop1 = Rule {
    case g @ CheckGoal(c, t, TopType) if t.isValue =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckTop1")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTop1 : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      Some((List(), _ => (true, CheckJudgment("CheckTop1", c, t, TopType))))
    case g =>
      None()
  }

  val CheckTop2 = Rule {
    case g @ CheckGoal(c, t, TopType) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckTop2")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTop2 : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckTop2", c, t, TopType))
          case _ =>
            (false, ErrorJudgment("CheckTop2", c, s"Could not check ${termOutput(t)} has type ${typeOutput(TopType)} with CheckTop2."))
        }
      ))
    case g =>
      None()
  }

  val InferUnfold = Rule {
    case g @ InferGoal(c, e @ Unfold(t1, Bind(x, t2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferUnfold")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnfold : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
         ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
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
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
          ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg2, fg3), {
          case Cons(InferJudgment(_, _, _, ty),
            Cons(InferJudgment(_, _, _, ty1),
            Cons(j3, _))) =>
            dropRefinements(ty) match {
              case IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty)))) =>
                if(TypeOperators.spos(a, ty)) (true, InferJudgment("InferUnfold", c, e, ty1))
                else (false, ErrorJudgment("InferUnfold", c, s"Could not infer type for ${termOutput(e)} with InferUnFold: $a does not appears strictly positively in ${typeOutput(ty)}"))

              case RecType(n, Bind(x, ty)) =>
                j3 match {
                  case InferJudgment(_, _, _, ty2) =>
                    if(ty1.areEqual(ty2)) (true, InferJudgment("InferUnfold", c, e, ty1))
                    else {
                      (
                        false,
                        ErrorJudgment(
                          "InferUnfold",
                          c,
                          s"Could not infer type for ${termOutput(e)} with InferFold: ${typeOutput(ty1)} not equal to ${typeOutput(ty2)}."
                        )
                      )
                    }
                  case _ => (false, ErrorJudgment("InferUnfold", c, s"Could not infer type for ${termOutput(e)} with InferFold."))
                }
               case _ =>
                (false, ErrorJudgment("InferUnfold", c, s"Could not infer type for ${termOutput(e)} with InferUnFold: expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}."))
            }
          case _ => (false, ErrorJudgment("InferUnfold", c, s"Could not infer type for ${termOutput(e)} with InferUnFold."))
        }
      ))

    case _ => None()
  }

  val NewInferUnfoldPositive = Rule {
    case g @ InferGoal(c, e @ UnfoldPositive(t1, Bind(x, t2))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferUnfoldPositive")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferUnfoldPositive : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
            case _ => ErrorGoal(c, s"Expecting a rec type for ${termOutput(t1)}, found ${typeOutput(ty)}.")
          }
        case _ =>
          ErrorGoal(c, s"Could not infer a type for ${termOutput(t1)}.")
      }
      Some((
        List(_ => g1, fg3), {
          case Cons(InferJudgment(_, _, _, _),
            Cons(InferJudgment(_, _, _, ty2), _)) =>
            (true, InferJudgment("NewInferUnfoldPositive", c, e, ty2))
          case _ => (false, ErrorJudgment("NewInferUnfoldPositive", c, s"Could not infer type for ${termOutput(e)} with InferUnFold."))
        }
      ))

    case _ => None()
  }

  val InferTypeAbs = Rule {
    case g @ InferGoal(c, e @ Abs(Bind(a, t))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferTypeAbs")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferTypeAbs : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferTypeAbs", c, e, PolyForallType(Bind(a, tpe))))
          case _ =>
            (false, ErrorJudgment("InferTypeAbs", c, s"Could not infer type for ${termOutput(e)} with InferTypeAbs."))
        }
      ))
    case g =>
      None()
  }

  val InferTypeApp = Rule {
    case g @ InferGoal(c, e @ TypeApp(t, ty)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferTypeApp")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferTypeApp : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, PolyForallType(Bind(x, tpe))), _) =>
            (true, InferJudgment("InferTypeApp", c, e, tpe.replace(x, ty)))
          case Cons(InferJudgment(_, _, _, ty), _) =>
            (false, ErrorJudgment("InferTypeApp", c,
              s"Could not infer type for ${termOutput(e)} with InferTypeApp: expecting poly forall type for ${termOutput(t)}, found ${typeOutput(ty)}."))
          case _ =>
            (false, ErrorJudgment("InferTypeApp", c, s"Could not infer type for ${termOutput(e)} with InferTypeApp."))
        }
      ))
    case g =>
      None()
  }

  val CheckTypeAbs = Rule {
    case g @ CheckGoal(c, t, tpe @ PolyForallType(Bind(a, ty))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}CheckTypeAbs")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} CheckTypeAbs : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = CheckGoal(c1, TypeApp(t, Var(a)), ty)
      Some((List(_ => subgoal),
        {
          case Cons(CheckJudgment(_, _, _, _), _) =>
            (true, CheckJudgment("CheckTypeAbs", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckTypeAbs", c, s"Could not check ${termOutput(t)} has type ${typeOutput(tpe)} with CheckTypeAbs."))
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
      TypeChecker.ruleNameDebug(s"${"   " * c.level}UnfoldRefinementInContext")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} UnfoldRefinementInContext : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val c1 = unfoldRefinementInContext(c)
      val subgoal = EqualityGoal(c1.incrementLevel(), t1, t2)
      Some((List(_ => subgoal),
        {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) =>
            (true, AreEqualJudgment("NewUnfoldRefinementInContext", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("NewUnfoldRefinementInContext", c, g.toString))
        }
      ))
    case g =>
      None()
  }

  val NewNatEqualToEqual = Rule {
    case g @ EqualityGoal(c, Primitive(Eq, Cons(t1, Cons(t2, Nil()))), BooleanLiteral(true)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewNatEqualToEqual")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewNatEqualToEqual: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")

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
            (false, ErrorJudgment("NewNatEqualToEqual", c, g.toString))
        }
      ))
    case g =>
      None()
  }


  val InferFoldGen = Rule {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty))))), t)) =>
      /* Fail if n != m */
      TypeChecker.ruleNameDebug(s"${"   " * c.level}InferFoldGen")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferFoldGen : ${g.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val nTy = IntersectionType(NatType, Bind(n, RecType(Var(n), Bind(a, ty))))
      val check = CheckGoal(c.incrementLevel(), t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => check),
        {
          case Cons(CheckJudgment(_, _, _, _), _) if TypeOperators.spos(a, ty) =>
            (true, InferJudgment("InferFoldGen", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferFoldGen", c, s"Could not infer type for ${termOutput(e)} with InferUnFoldGen."))
        }
      ))
    case g =>
      None()
  }


  val NewEqualityInContext = Rule {
    case g @ EqualityGoal(c, t1, t2) if
      c.variables.exists(v =>
        c.termVariables(v) == EqualityType(t1,t2) ||
        c.termVariables(v) == EqualityType(t2,t1)
      )
      =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}EqualityInContext")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} EqualityInContext: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
    case Cons(v, vs) => termVariables(v) match {
      case EqualityType(Var(id2), t) if id == id2 =>
        Some(t)
      case EqualityType(t, Var(id2)) if id == id2 && !t.isInstanceOf[Var] =>
        Some(t)
      case _ => findEquality(vs, termVariables, id)
    }
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
    case Cons(v, vs) =>
      expandVars(c.copy(variables = l.tail), c.termVariables(v)).map(
        ty => c.copy(termVariables = c.termVariables.updated(v, ty))
      ) orElse expandVars(c, vs)
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
      case Cons(v, vs) =>
        lift(f, c.copy(variables = vs), c.termVariables(v)).map {
          case (e, a) =>
            (c.copy(termVariables = c.termVariables.updated(v, e)), a)
        } orElse {
          lift(f, c, vs)
        }
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
        TypeChecker.ruleNameDebug(s"${"   " * c.level}NewExpandVars")
        TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewExpandVars : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
        (List(_ => sg), {
          case Cons(AreEqualJudgment(_, _, _, _, _), _) =>
            (true, AreEqualJudgment("NewExpandVars", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("NewExpandVars", c, g.toString))
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
            case _ => ErrorGoal(c, s"Attempted to inline an application or a val, but could not type check the argument.")
          }
          (List(_ => subgoal, newGoal), {
            case Cons(_, Cons(AreEqualJudgment(_, _, _, _, _), _)) =>
              (true, AreEqualJudgment("NewInlineApplications", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("NewInlineApplications", c, g.toString))
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
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopIf")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopIf : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topIf(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ IfThenElse(tc, tt, tf)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopIf")
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
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopMath")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopMath : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ Match(tc, tt, tf)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopEitherMath")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopEitherMath : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ EitherMatch(tc, tt, tf)) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewTopEitherMatch")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewTopEitherMatch : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      topEitherMatch(c, t2, t1)
    case g =>
      None()
  }

  val InferTypeDefinition = Rule {
    case g @ InferGoal(c, e @ TypeDefinition(ty, Bind(id, t))) =>
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} InferTypeDefinition : ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
      val subgoal = InferGoal(c, t.replace(id, ty))
      Some((List(_ => subgoal),
        {
          case Cons(InferJudgment(_, _, _, tpe), _) =>
            (true, InferJudgment("InferTypeDefinition", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferTypeDefinition", c, g.toString))
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

  def z3Encode(z3: Z3Context, solver: Z3Solver, variables: Map[Identifier, Z3AST], t: Tree): Z3AST = {
    t match {
      case Var(id) if variables.contains(id) => variables(id)
      case NatLiteral(n) => z3.mkInt(n.toInt, z3.mkIntSort())
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

  val NewZ3ArithmeticSolver = Rule {
    case g @ EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, Cons(t1, Cons(t2, Nil())))) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}Z3ArithmeticSolver")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} Z3ArithmeticSolver: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
    case g @ EqualityGoal(c, t1, t2) if t1.areEqual(t2) =>
      TypeChecker.ruleNameDebug(s"${"   " * c.level}NewReflexivity")
      TypeChecker.typeCheckDebug(s"${"   " * c.level}Current goal ${g} NewReflexivity: ${c.toString.replaceAll("\n", s"\n${"   " * c.level}")}\n")
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
    case g @ SynthesisGoal(c, tp) if c.containsVarOfType(tp) =>
      Some((List(), _ => (true, SynthesisJudgment("NewSynthesisVar", c, NatType, Var(c.getVarOfType(tp).get)))))
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
            (false, ErrorJudgment("NewSynthesisPi", c, s"Could not synthesize term of type ${typeOutput(tp)}."))
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
          ErrorGoal(c, s"Could not synthesize term of type ${typeOutput(ty1)}.")
      }
      Some((
        List(_ => g1, fg2),
        {
          case Cons(SynthesisJudgment(_, _, _, t1), Cons(SynthesisJudgment(_, _, _, t2), _)) =>
            (true, SynthesisJudgment("NewSynthesisSigma", c, tp, Pair(t1, t2)))
          case _ =>
            (false, ErrorJudgment("NewSynthesisSigma", c, s"Could not synthesize term of type ${typeOutput(tp)}."))
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
            (false, ErrorJudgment("NewSynthesisSum", c, s"Could not synthesize term of type ${typeOutput(tp)}."))
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
