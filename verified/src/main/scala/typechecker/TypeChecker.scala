package typechecker

import _root_.trees._
import _root_.interpreter._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

case class Context(
  val variables: List[Identifier],
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Tree],
  val termEqualities: List[(Tree, Tree)],
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
) {
  def bind(i: Identifier, t: Tree) = {
    if(variables.contains(i)) throw new java.lang.Exception(s"Already bound ${i}")
    copy(
      termVariables = termVariables.updated(i, t),
      variables = i::variables
    )
  }

  def bindFresh(s: String, t: Tree) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree) = copy(termEqualities = (t1, t2)::termEqualities)

  override def toString: String = {
    "Term equalities:\n"++
    termEqualities.foldLeft("") {
      case (acc, (a, b)) => acc + s"${a} = ${b}\n"
    }++ "Term variables:\n" ++
    variables.foldLeft("") {
      case (acc, id) => acc + s"${id}: ${termVariables(id)}\n"
    }
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
  val level: Int
}

case class InferGoal(c: Context, t: Tree, level: Int) extends Goal {
  override def toString: String = {
    s"Inferring ${t}"
  }
}

case class CheckGoal(c: Context, t: Tree, tp: Tree, level: Int) extends Goal {
  override def toString: String = {
    s"Checking ${t}: ${tp}"
  }
}

case class SynthesizeGoal(c: Context, tp: Tree, level: Int) extends Goal

case class EqualityGoal(c: Context, t1: Tree, t2: Tree, level: Int) extends Goal {
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


sealed abstract class Result

case class InferResult(ty: Tree) extends Result
case class CheckResult(b: Boolean) extends Result
case class SynthesizeResult(t: Tree) extends Result
case class EqualityResult(b: Boolean) extends Result
case object ErrorResult extends Result

case class ResultGoalContext(
  val goals: List[ResultGoalContext => Goal],
  val results: Map[Goal, Result],
  val merge: ResultGoalContext => ResultGoalContext
) {
  def updateResults(goal: Goal, result: Result) = {
    copy(
      results = results.updated(goal, result)
    )
  }

  override def toString: String = {
    results.theMap.foldLeft("") {
      case (acc, (g, r)) => acc + s"${g} = ${r}\n"
    }
  }
}


object TypeSimplification {
  private def simpl(t1: Tree, t2: Tree, f: (Tree, Tree) => Tree): Tree = {
    (t1, t2) match {
      case (UnitType, UnitType) => UnitType
      case (NatType, NatType) => NatType
      case (BoolType, BoolType) => BoolType
      case (TopType, TopType) => TopType
      case (PiType(a1, Bind(x, b1)), PiType(a2, Bind(x2, b2))) =>
        PiType(simpl(a1, a2, f), Bind(x, simpl(b1, Interpreter.replace(x2, Var(x), b2), f)))
      case (IntersectionType(a1, Bind(x, b1)), IntersectionType(a2, Bind(x2, b2))) =>
        IntersectionType(simpl(a1, a2, f), Bind(x, simpl(b1, Interpreter.replace(x2, Var(x), b2), f)))
      case (PolyForallType(Bind(x, b1)), PolyForallType(Bind(x2, b2))) =>
        PolyForallType(Bind(x, simpl(b1, Interpreter.replace(x2, Var(x), b2), f)))
      case (SigmaType(a1, Bind(x, b1)), SigmaType(a2, Bind(x2, b2))) =>
        SigmaType(simpl(a1, a2, f), Bind(x, simpl(b1, Interpreter.replace(x2, Var(x), b2), f)))
      case (RefinementType(a1, Bind(x, p1)), RefinementType(a2, Bind(x2, p2))) =>
        RefinementType(simpl(a1, a2, f), Bind(x, f(p1, Interpreter.replace(x2, Var(x), p2))))
      case (RefinementType(a1, Bind(x, p1)), t3) => RefinementType(simpl(a1, t3, f), Bind(x, p1))
      case (t3, RefinementType(a1, Bind(x, p1))) => RefinementType(simpl(a1, t3, f), Bind(x, p1))
      case (EqualityType(t11, t12), EqualityType(t21, t22)) =>
        EqualityType(f(t11, t21), f(t12, t22))
      case (_, _) => BottomType
    }
  }

  def ifThenElse(tc: Tree, t1: Tree, t2: Tree): Tree = {
    if(t1 == t2) t1
    else simpl(t1, t2, (ty1: Tree, ty2: Tree) => IfThenElse(tc, ty1, ty2))
  }

  def matchSimpl(n: Tree, t0: Tree, id: Identifier, tn: Tree): Tree = {
    simpl(t0, tn, (ty0: Tree, tyn: Tree) => Match(n, ty0, Bind(id, tyn)))
  }

  def eitherMatch(n: Tree, idl: Identifier, tl: Tree, idr: Identifier, tr: Tree): Tree = {
    simpl(tl, tr, (tyl: Tree, tyr: Tree) => EitherMatch(n, Bind(idl, tyl), Bind(idr, tyr)))
  }

  def letIn(x: Identifier, tp: Option[Tree], v: Tree, t: Tree) = {
    def f(t1: Tree, t2: Tree): Tree = {
      if(x.isFreeIn(t1)) LetIn(tp, v, Bind(x, t1))
      else t1
    }
    simpl(t, t, f)
  }
}

trait Rule {
  def apply(g: Goal): ResultGoalContext

  val errorContext: ResultGoalContext =
    ResultGoalContext(
      Nil(),
      Map(),
      (rc: ResultGoalContext) => rc
    )

  def or(other: Rule): Rule = Rule.or(this, other)
  def repeat: Rule = Rule.repeat(this)
  def ||(other: Rule): Rule = Rule.or(this, other)
}



object Rule {
  def or(rule1: Rule, rule2: Rule): Rule = {
    new Rule {
      def apply(g: Goal): ResultGoalContext = {
        val rc1: ResultGoalContext = rule1.apply(g)
        if(rc1 == errorContext) rule2.apply(g) else rc1
      }
    }
  }

  def repeat(rule: Rule): Rule = {
    new Rule {
      def apply(g: Goal): ResultGoalContext = {
        val rc = rule.apply(g)
        if(rc.goals.isEmpty) {
          rc.merge(rc)
        }
        else {
          val rrc = rc.goals.foldLeft(rc) { case (rc, g) =>
            val newRc = apply(g(rc))
            //val ret = rc.merge(newRc)
            ResultGoalContext(
              List(),
              rc.results ++ newRc.results, // ++ ret.results,
              (withRes: ResultGoalContext) => rc.merge(withRes)
            )
          }
          rrc.merge(rrc)
        }
      }
    }
  }
}


case object NewErrorGoalRule extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    errorContext
  }
}

case object InferBool extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, BoolLiteral(b), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferBool : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(BoolType)),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(BoolType)) }
        )
      case _ => errorContext
    }
  }
}

case object CheckReflexive extends Rule {
  def drop(t: Tree): Tree = {
    t match {
      case RefinementType(ty, _) => drop(ty)
      case _ => t
    }
  }

  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, t, ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckReflexive : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val gInfer = InferGoal(c, t, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gInfer),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gInfer) match {
              case Some(InferResult(ty1)) =>
                rc.updateResults(
                  g,
                  CheckResult(drop(ty1) == ty)
                )
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferNat extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, NatLiteral(n), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferNat : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(NatType)),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(NatType)) }
        )
      case _ => errorContext
    }
  }
}

case object InferUnit extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, UnitLiteral, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferUnit : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(UnitType)),
          (rc: ResultGoalContext) => rc.updateResults(g, InferResult(UnitType))
        )
      case _ => errorContext
    }
  }
}

case object InferVar extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Var(id), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferVar : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        ResultGoalContext(
          Nil(),
          c.getTypeOf(id) match {
            case Some(ty) =>
              Map(g -> InferResult(ty))
            case None() => Map()
          },
          c.getTypeOf(id) match {
            case Some(ty) => (rc: ResultGoalContext) => rc.updateResults(g, InferResult(ty))
            case None() => (rc: ResultGoalContext) => rc
          }
        )
      case _ => errorContext
    }
  }
}

case object InferError extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, ErrorTree(_, tp), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferError : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val ty = tp.getOrElse(UnitType)
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(ty)),
          (rc: ResultGoalContext) => rc.updateResults(g, InferResult(ty))
        )
      case _ => errorContext
    }
  }
}


case object InferApp extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, App(t1, t2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferApp : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val g1 = InferGoal(c, t1, g.level + 1)
        val fg2 = (rc: ResultGoalContext) => {
          rc.results.get(g1) match {
            case Some(InferResult(PiType(ty2, Bind(_, ty)))) =>
              CheckGoal(c, t2, ty2, l + 1)
            case Some(ty) =>
              ErrorGoal(c, s"Error in InferApp ${t1}.\n\nInfer${ty}\n\n\n")
            case _ =>
              ErrorGoal(c, s"Error in InferApp None ${t1}")
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => g1, fg2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(g1), rc.results.get(fg2(rc))) match {
              case (Some(InferResult(PiType(_, Bind(x, ty)))), Some(CheckResult(true))) =>
                val t = TypeSimplification.letIn(x, None(), t2, ty)
                rc.updateResults(g, InferResult(t))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferLambda extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Lambda(Some(ty1), Bind(id, body)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferLambda : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val c1 = c.bind(id, ty1)
        val gb = InferGoal(c1, body, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gb) match {
              case Some(InferResult(bodyTy)) =>
                rc.updateResults(
                  g,
                  InferResult(PiType(ty1, Bind(id, bodyTy)))
                )
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferBinNatPrimitive extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Primitive(op, Cons(n1, Cons(n2, Nil()))), l) if Operator.isNatBinOp(op) =>
        TypeChecker.typeCheckDebug(s"${"   " * l}Current goal InferBinNatPrimitive : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkN1 = CheckGoal(c, n1, NatType, g.level + 1)
        val checkN2 = CheckGoal(c, n2, NatType, g.level + 1)
        val retType = if(Operator.isNatToBoolBinOp(op)) BoolType else NatType
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkN1, (rc: ResultGoalContext) => checkN2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(checkN1), rc.results.get(checkN2)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true))) => rc.updateResults(g, InferResult(retType))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferBinBoolPrimitive extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Primitive(op, Cons(b1, Cons(b2, Nil()))), l) if Operator.isBoolBinOp(op) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferBinBoolPrimitive : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkB1 = CheckGoal(c, b1, BoolType, g.level + 1)
        val checkB2 = CheckGoal(c, b2, BoolType, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkB1, (rc: ResultGoalContext) => checkB2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(checkB1), rc.results.get(checkB2)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true))) => rc.updateResults(g, InferResult(BoolType))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferUnBoolPrimitive extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Primitive(op, Cons(b, Nil())), l) if Operator.isBoolUnOp(op) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferUnBoolPrimitive : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkB = CheckGoal(c, b, BoolType, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkB),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(checkB) match {
              case Some(CheckResult(true)) => rc.updateResults(g, InferResult(BoolType))
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
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferDropRefinement : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val inferGoal = InferGoal(c, t, g.level + 1)
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

case object InferLet extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, LetIn(None(), v, Bind(id, body)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferLet : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val gv = InferGoal(c, v, g.level + 1)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(tyv)) =>
              val c1 = c.bind(id, tyv).addEquality(Var(id), v)
              InferGoal(c1, body, l + 1)
            case _ => ErrorGoal(c, s"Error in InferLet ${g}")
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, fgb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(fgb(rc)) match {
              case Some(InferResult(ty)) =>
                val retTy = TypeSimplification.letIn(id, None(), v, ty)
                rc.updateResults(g, InferResult(retTy))
              case _ => rc
            }
          }
        )
      case InferGoal(c, LetIn(Some(tyv), v, Bind(id, body)), l) =>
        val gv = CheckGoal(c, v, tyv, g.level + 1)
        val c1 = c.bind(id, tyv).addEquality(Var(id), v)
        val gb = InferGoal(c1, body, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, (rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(gv), rc.results.get(gb)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty))) =>
                val retTy = TypeSimplification.letIn(id, Some(tyv), v, ty)
                rc.updateResults(g, InferResult(retTy))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferIf extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, IfThenElse(tc, t1, t2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferIf : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val c1 = c.addEquality(tc, BoolLiteral(true))
        val c2 = c.addEquality(tc, BoolLiteral(false))
        val checkCond = CheckGoal(c, tc, BoolType, g.level + 1)
        val inferT1 = InferGoal(c1, t1, g.level + 1)
        val inferT2 = InferGoal(c2, t2, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => inferT1, (r: ResultGoalContext) => inferT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(inferT1), rc.results.get(inferT2)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                val t = TypeSimplification.ifThenElse(tc, ty1, ty2)
                rc.updateResults(g, InferResult(t))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferLeft extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, LeftTree(t), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferLeft : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, t, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(ty1)) =>
                rc.updateResults(g, InferResult(SumType(ty1, BottomType)))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferRight extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, RightTree(t), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferRight : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, t, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(ty2)) =>
              rc.updateResults(g, InferResult(SumType(BottomType, ty2)))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferPair extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Pair(t1, t2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferPair : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val inferFirst = InferGoal(c, t1, g.level + 1)
        val inferSecond = InferGoal(c, t2, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => inferFirst, (r: ResultGoalContext) => inferSecond),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(inferFirst), rc.results.get(inferSecond)) match {
              case (Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                rc.updateResults(g, InferResult(SigmaType(ty1, Bind(Identifier(0, "X"), ty2))))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferFirst extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, First(t), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferFirst : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, t, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SigmaType(ty1, _))) => rc.updateResults(g, InferResult(ty1))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferSecond extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Second(t), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferSecond : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, t, g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SigmaType(ty1, Bind(x, ty2)))) =>
                val retTy = TypeSimplification.letIn(x, None(), First(t), ty2)
                rc.updateResults(g, InferResult(retTy))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferMatch extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Match(t, t0, Bind(id, tn)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferMatch : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val c1 = c.addEquality(tn, NatLiteral(0))
        val c2 = c.bind(id, NatType).addEquality(
          tn,
          Primitive(
            Plus,
            List(Var(id), NatLiteral(1))
          )
        )
        val checkCond = CheckGoal(c, t, NatType, g.level + 1)
        val inferT0 = InferGoal(c1, t0, g.level + 1)
        val inferTn = InferGoal(c2, tn, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => inferT0, (r: ResultGoalContext) => inferTn),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(inferT0), rc.results.get(inferTn)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty0)), Some(InferResult(tyn))) =>
                val retTy = TypeSimplification.matchSimpl(t, ty0, id, tyn)
                rc.updateResults(g, InferResult(retTy))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferEitherMatch extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferEitherMatch : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val inferVar = InferGoal(c, t, g.level + 1)
        val finferT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c1 = c.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1, l + 1)
            case _ => ErrorGoal(c, s"Error in InferEitherMatch ${g}")
          }
        }
        val finferT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c2 = c.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2, l + 1)
            case _ => ErrorGoal(c, s"Error in InferEitherMatch ${g}")
          }
        }
        ResultGoalContext(
          List((r: ResultGoalContext) => inferVar, finferT1, finferT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(finferT1(rc)), rc.results.get(finferT2(rc))) match {
              case (Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                val retTy = TypeSimplification.eitherMatch(t, id1, ty1, id2, ty2)
                rc.updateResults(g, InferResult(retTy))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object InferFix extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t))), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferFix : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")

        // If n1 != n, fail
        val m = Identifier(0, "_M")
        val c1 = c.bind(n, NatType).bind(
          y,
          PiType(UnitType, Bind(Identifier(0, "_"),
            IntersectionType(
              RefinementType(NatType, Bind(m, Primitive(Lt, List(Var(m), Var(n))))),
              Bind(m, Interpreter.replace(n, Var(m), ty)))) // TODO ty with n replaced by m
          )
        ).addEquality(
          Var(y),
          Lambda(
            Some(UnitType),
            Bind(Identifier(0, "_Unit"), Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))))
        )
        val subgoal = CheckGoal(c1, t, ty, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
             rc.results.get(subgoal) match {
              case Some(CheckResult(true)) =>
                rc.updateResults(g, InferResult(IntersectionType(NatType, Bind(n, ty))))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferIntersection extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case InferGoal(c, Inst(t1, t2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal InferIntersection : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val inferT1 = InferGoal(c, t1, g.level + 1)
        val fcheckT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferT1) match {
            case Some(InferResult(IntersectionType(ty1, Bind(_, ty)))) =>
              CheckGoal(c, t2, ty1, l + 1)
            case _ => ErrorGoal(c, s"Error in Intersection ${g}")
          }
        }
        ResultGoalContext(
          List((r: ResultGoalContext) => inferT1, fcheckT2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(inferT1), rc.results.get(fcheckT2(rc))) match {
              case (Some(InferResult(IntersectionType(ty1, Bind(x, ty)))), Some(CheckResult(true))) =>
                val t = TypeSimplification.letIn(x, None(), t2, ty)
                rc.updateResults(g, InferResult(t))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object CheckIf extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, IfThenElse(tc, t1, t2), ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckIf : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val c1 = c.addEquality(tc, BoolLiteral(true))
        val c2 = c.addEquality(tc, BoolLiteral(false))
        val checkCond = CheckGoal(c, tc, BoolType, g.level + 1)
        val checkT1 = CheckGoal(c1, t1, ty, g.level + 1)
        val checkT2 = CheckGoal(c2, t2, ty, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => checkT1, (r: ResultGoalContext) => checkT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(checkT1), rc.results.get(checkT2)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true)), Some(CheckResult(true))) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckMatch extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, Match(t, t0, Bind(id, tn)), ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckMatch : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val c1 = c.addEquality(tn, NatLiteral(0))
        val c2 = c.bind(id, NatType).addEquality(
          tn,
          Primitive(
            Plus,
            List(Var(id), NatLiteral(1))
          )
        )
        val checkCond = CheckGoal(c, t, NatType, g.level + 1)
        val checkT0 = CheckGoal(c1, t0, ty, g.level + 1)
        val checkTn = CheckGoal(c2, tn, ty, g.level + 1)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => checkT0, (r: ResultGoalContext) => checkTn),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(checkT0), rc.results.get(checkTn)) match {
              case (Some(CheckResult(true)), Some(CheckResult(true)), Some(CheckResult(true))) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckEitherMatch extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckEitherMatch : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val inferVar = InferGoal(c, t, g.level + 1)
        val fcheckT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c1 = c.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, ty, g.level + 1)
            case _ => ErrorGoal(c, s"Error in CheckEitherMatch ${g}")
          }
        }
        val fcheckT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c2 = c.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              CheckGoal(c2, t2, ty, g.level + 1)
            case _ => ErrorGoal(c, s"Error in CheckEitherMatch ${g}")
          }
        }
        ResultGoalContext(
          List((r: ResultGoalContext) => inferVar, fcheckT1, fcheckT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(fcheckT1(rc)), rc.results.get(fcheckT2(rc))) match {
              case (Some(CheckResult(true)), Some(CheckResult(true))) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckLet extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, LetIn(None(), v, Bind(id, body)), ty, l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckLet : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val gv = InferGoal(c, v, g.level + 1)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(tyv)) =>
              val c1 = c.bind(id, tyv).addEquality(Var(id), v)
              CheckGoal(c1, body, ty, g.level + 1)
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
        val gv = CheckGoal(c, v, tyv, g.level + 1)
        val c1 = c.addEquality(Var(id), v)
        val gb = CheckGoal(c1, body, ty, g.level + 1)
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
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckIntersection : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val (freshId, c1) = c.bindFresh(id.name, tyid)
        val subgoal = CheckGoal(c1, Inst(t, Var(freshId)), ty, g.level + 1)
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


case object CheckPi extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, t, PiType(ty1, Bind(id, ty2)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckPi : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val (freshId, c1) = c.bindFresh(id.name, ty1)
        val subgoal = CheckGoal(c1, App(t, Var(freshId)), ty2, g.level + 1)
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

case object CheckSigma extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, t, SigmaType(ty1, Bind(id, ty2)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckSigma : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkFirst = CheckGoal(c, First(t), ty1, g.level + 1)
        val fcheckSecond = (rc: ResultGoalContext) => {
          rc.results.get(checkFirst) match {
            case Some(CheckResult(true)) =>
              val c1 = c.bind(id, ty1).addEquality(Var(id), First(t))
              CheckGoal(c1, Second(t), ty2, g.level + 1)
            case _ => ErrorGoal(c,  s"Error in CheckSigma ${g}")
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkFirst, fcheckSecond),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(checkFirst), rc.results.get(fcheckSecond(rc))) match {
              case (Some(CheckResult(true)), Some(CheckResult(true))) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckLeft extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, LeftTree(t), SumType(ty1, ty2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckLeft : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, LeftTree(t), g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SumType(typ1, typ2))) => rc.updateResults(g, CheckResult(ty1 == typ1))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckRight extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, RightTree(t), SumType(ty1, ty2), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckRight : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val subgoal = InferGoal(c, RightTree(t), g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SumType(typ1, typ2))) => rc.updateResults(g, CheckResult(ty2 == typ2))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object CheckRefinement extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case CheckGoal(c, t, RefinementType(ty, Bind(id, b)), l) =>
        TypeChecker.typeCheckDebug(s"${"   " * g.level}Current goal CheckRefinement : ${g.toString.replaceAll("\n", s"\n${"   " * g.level}")}\n")
        val checkTy = CheckGoal(c, t, ty, g.level + 1)
        val c1 = c.bind(id, ty).addEquality(Var(id), t)
        val checkRef = EqualityGoal(c1, b, BoolLiteral(true), g.level + 1)
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkTy, (rc: ResultGoalContext) => checkRef),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(checkTy), rc.results.get(checkRef)) match { //, rc.results.get(fcheckSecond(rc))) match {
              case (Some(CheckResult(true)), Some(EqualityResult(true))) =>
                rc.updateResults(g, CheckResult(true))
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
        case Var(id) => Interpreter.replace(id, v2, acc)
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
        val subgoal = EqualityGoal(c1, newT1, newT2, g.level + 1)
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
          val t2p = Interpreter.replace(y, Var(x), t2)
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
        val subgoal =  EqualityGoal(c1, t1, t2, g.level + 1)
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
        val subgoal =  CheckGoal(c, n1, NatType, g.level + 1)
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



case object EqualityResolve extends Rule {
  def apply(g: Goal): ResultGoalContext = {

    g match  {
      case EqualityGoal(c, t1, t2, l) =>
        TypeChecker.equalityDebug(s"Context:\n${c}\n")
        TypeChecker.equalityDebug(s"Equality between ${t1} and ${t2} to solve.\n\n")
        ResultGoalContext(
          Nil(),
          Map(g -> EqualityResult(true)),
          (rc: ResultGoalContext) => { rc.updateResults(g, EqualityResult(true)) }
        )
      case _ => errorContext
    }
  }
}


case object PrintRule extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    throw new java.lang.Exception(s"Goal is not handled ${g}")
  }
}


object TypeChecker {
  val rule = InferBool || InferNat || InferApp || InferUnit || InferVar || InferLambda || CheckLeft || CheckRefinement || CheckPi ||
       CheckRight || NewErrorGoalRule || InferBinNatPrimitive || InferLet || InferIf || InferPair || InferFirst || InferSecond || InferMatch ||
    CheckIf || CheckMatch || InferEitherMatch || InferError || InferBinBoolPrimitive || InferUnBoolPrimitive || InferLeft || InferRight ||
    InferFix || InferIntersection|| ReplaceLet || NatInequalityResolve || GoodArithmeticResolve ||  ReflexivityResolve || NoName1Resolve || NoName2Resolve || InContextResolve || EqualityResolve || CheckSigma || CheckReflexive || InferDropRefinement || PrintRule

  val tdebug = false
  val edebug = false

  def infer(t: Tree, max: Int) = {
    val g = InferGoal(Context(List(), Map(), Set(), List(), max), t, 0)
    val c = rule.repeat.apply(g)
    c.results.getOrElse(g, ErrorResult)
  }

  def typeCheckDebug(s: String): Unit = {
    if(tdebug) println(s)
  }

  def equalityDebug(s: String): Unit = {
    if(edebug) println(s)
  }
}