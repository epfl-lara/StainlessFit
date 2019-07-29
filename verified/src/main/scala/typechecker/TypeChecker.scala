package typechecker

import _root_.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

case class Context(
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Tree],
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
) {
  def bind(i: Identifier, t: Tree) = copy(termVariables = termVariables.updated(i, t))
  def bindFresh(s: String, t: Tree) = bind(Identifier(n, s), t).copy(n = n+1)

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)
}

sealed abstract class Goal {
  val c: Context
}

case class InferGoal(c: Context, t: Tree) extends Goal
case class CheckGoal(c: Context, t: Tree, tp: Tree) extends Goal
case class SynthesizeGoal(c: Context, tp: Tree) extends Goal
case class ErrorGoal(c: Context) extends Goal


sealed abstract class Result

case class InferResult(ty: Tree) extends Result
case class CheckResult(b: Boolean) extends Result
case class SynthesizeResult(t: Tree) extends Result
case object ErrorResult extends Result

case class ResultGoalContext(
  val goals: List[ResultGoalContext => Goal],
  val results: Map[Goal, Result],
  val merge: ResultGoalContext => ResultGoalContext
) {
  def updateResults(goal: Goal, result: Result) = {
    copy(results = results.updated(goal, result))
  }
}


object TypeSimplification {
  def simpl(t2: Tree, t3: Tree): Tree = {
    (t2, t3) match {
      case (UnitType, UnitType) => UnitType
      case (NatType, NatType) => NatType
      case (BoolType, BoolType) => BoolType
      case (TopType, TopType) => TopType
      case (PiType(a1, Bind(x, b1)), PiType(a2, Bind(_, b2))) => PiType(simpl(a1, a2), Bind(x, simpl(b1, b2)))
      case (PolyForallType(a1, Bind(x, b1)), PolyForallType(a2, Bind(_, b2))) => PolyForallType(simpl(a1, a2), Bind(x, simpl(b1, b2)))
      case (SigmaType(a1, Bind(x, b1)), SigmaType(a2, Bind(_, b2))) => SigmaType(simpl(a1, a2), Bind(x, simpl(b1, b2)))
      case (RefinementType(a1, Bind(x, p1)), RefinementType(a2, Bind(_, p2))) => RefinementType(simpl(a1, a2), Bind(x, simpl(p1, p2)))
      case (RefinementType(a1, Bind(x, p1)), t) => RefinementType(simpl(a1, t), Bind(x, p1))
      case (t, RefinementType(a1, Bind(x, p1))) => RefinementType(simpl(a1, t), Bind(x, p1))
      case (EqualityType(t11, t12), EqualityType(t21, t22)) => EqualityType(simpl(t11, t21), simpl(t12, t22))
      case (_, _) => BottomType
    }
  }

  /*def if(t1, t2, t3): Tree = simpl(t2, t3)

  def match(tn, t1, b): Tree = {
    b match {
      case Bind(n, t2) => simpl(t1, t2)
      case _ => BottomType
    }
  }

  def letin(t1, t2): Tree = simpl(t2, t2)*/
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
    g match {
      case InferGoal(c, BoolLiteral(b)) =>
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
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, t, ty) =>
        val gInfer = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gInfer),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gInfer) match {
              case Some(InferResult(ty1)) =>
                rc.updateResults(
                  g,
                  CheckResult(ty1 == ty)
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
    g match {
      case InferGoal(c, NatLiteral(n)) =>
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
    g match {
      case InferGoal(c, UnitLiteral) =>
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
    g match {
      case InferGoal(c, Var(id)) =>
        ResultGoalContext(
          Nil(),
          c.getTypeOf(id) match {
            case Some(ty) => Map(g -> InferResult(ty))
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
    g match {
      case InferGoal(c, ErrorTree(_, tp)) =>
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
    g match {
      case InferGoal(c, App(t1, t2)) =>
        val g1 = InferGoal(c, t1)
        val fg2 = (rc: ResultGoalContext) => {
          rc.results.get(g1) match {
            case Some(InferResult(PiType(ty2, Bind(_, ty)))) =>
              CheckGoal(c, t2, ty2)
            case _ =>
              ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => g1, fg2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(g1), rc.results.get(fg2(rc))) match {
              case (Some(InferResult(PiType(_, Bind(_, ty)))), Some(CheckResult(true))) =>
                rc.updateResults(g, InferResult(TypeSimplification.simpl(ty, ty)))
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
    g match {
      case InferGoal(c, Lambda(Some(ty1), Bind(id, body))) =>
        val c1 = c.bind(id, ty1)
        val gb = InferGoal(c1, body)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gb) match {
              case Some(InferResult(bodyTy)) =>
                rc.updateResults(
                  g,
                  InferResult(PiType(ty1, Bind(Identifier(0, "_"), bodyTy)))
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
    g match {
      case InferGoal(c, Primitive(op, Cons(n1, Cons(n2, Nil())))) if Operator.isNatBinOp(op) =>
        val checkN1 = CheckGoal(c, n1, NatType)
        val checkN2 = CheckGoal(c, n2, NatType)
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
    g match {
      case InferGoal(c, Primitive(op, Cons(b1, Cons(b2, Nil())))) if Operator.isBoolBinOp(op) =>
        val checkB1 = CheckGoal(c, b1, BoolType)
        val checkB2 = CheckGoal(c, b2, BoolType)
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
    g match {
      case InferGoal(c, Primitive(op, Cons(b, Nil()))) if Operator.isBoolUnOp(op) =>
        val checkB = CheckGoal(c, b, BoolType)
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


case object InferLet extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, LetIn(None(), v, Bind(id, body))) =>
        val gv = InferGoal(c, v)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(tyv)) =>
              val c1 = c.bind(id, tyv).bindFresh("_", EqualityType(Var(id), v))
              InferGoal(c1, body)
            case _ => ErrorGoal(c)
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
      case InferGoal(c, LetIn(Some(tyv), v, Bind(id, body))) =>
        val gv = CheckGoal(c, v, tyv)
        val c1 = c.bind(id, tyv).bindFresh("_", EqualityType(Var(id), v))
        val gb = InferGoal(c1, body)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, (rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(gv), rc.results.get(gb)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty))) =>
                rc.updateResults(g, InferResult(TypeSimplification.simpl(ty, ty)))
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
    g match {
      case InferGoal(c, IfThenElse(tc, t1, t2)) =>
        val c1 = c.bindFresh("_", EqualityType(tc, BoolLiteral(true)))
        val c2 = c.bindFresh("_", EqualityType(tc, BoolLiteral(false)))
        val checkCond = CheckGoal(c, tc, BoolType)
        val inferT1 = InferGoal(c1, t1)
        val inferT2 = InferGoal(c2, t2)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => inferT1, (r: ResultGoalContext) => inferT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(inferT1), rc.results.get(inferT2)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                val t = TypeSimplification.simpl(ty1, ty2)
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
    g match {
      case InferGoal(c, LeftTree(t)) =>
        val subgoal = InferGoal(c, t)
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
    g match {
      case InferGoal(c, RightTree(t)) =>
        val subgoal = InferGoal(c, t)
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
    g match {
      case InferGoal(c, Pair(t1, t2))  =>
        val inferFirst = InferGoal(c, t1)
        val inferSecond = InferGoal(c, t2)
        ResultGoalContext(
          List((r: ResultGoalContext) => inferFirst, (r: ResultGoalContext) => inferSecond),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(inferFirst), rc.results.get(inferSecond)) match {
              case (Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                rc.updateResults(g, InferResult(SigmaType(ty1, Bind(Identifier(0, "_"), ty2))))
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
    g match {
      case InferGoal(c, First(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SigmaType(ty1, ty2))) => rc.updateResults(g, InferResult(ty1))
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
    g match {
      case InferGoal(c, Second(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(SigmaType(ty1, ty2))) =>
                val t = TypeSimplification.simpl(ty2, ty2)
                rc.updateResults(g, InferResult(t))
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
    g match {
      case InferGoal(c, Match(t, t0, Bind(id, tn))) =>
        val c1 = c.bindFresh("_", EqualityType(tn, NatLiteral(0)))
        val c2 = c.bindFresh("_", EqualityType(tn, Succ(Var(id)))).bind(id, NatType)
        val checkCond = CheckGoal(c, t, NatType)
        val inferT0 = InferGoal(c1, t0)
        val inferTn = InferGoal(c2, tn)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => inferT0, (r: ResultGoalContext) => inferTn),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(inferT0), rc.results.get(inferTn)) match {
              case (Some(CheckResult(true)), Some(InferResult(ty0)), Some(InferResult(tyn))) =>
                val t = TypeSimplification.simpl(ty0, tyn)
                rc.updateResults(g, InferResult(t))
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
    g match {
      case InferGoal(c, EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
        val inferVar = InferGoal(c, t)
        val finferT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c1 = c.bindFresh("_", EqualityType(t, LeftTree(Var(id1)))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c)
          }
        }
        val finferT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c2 = c.bindFresh("_", EqualityType(t, RightTree(Var(id2)))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((r: ResultGoalContext) => inferVar, finferT1, finferT2),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(finferT1(rc)), rc.results.get(finferT2(rc))) match {
              case (Some(InferResult(ty1)), Some(InferResult(ty2))) =>
                val t = TypeSimplification.simpl(ty1, ty2)
                rc.updateResults(g, InferResult(t))
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
    g match {
      case InferGoal(c, Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) =>
        // If n1 != n, fail
        val m = Identifier(0, "_m")
        val c1 = c.bind(n, NatType).bind(
          y,
          PiType(UnitType, Bind(Identifier(0, "_"), PolyForallType(
            RefinementType(NatType, Bind(m, Primitive(Lt, List(Var(m), Var(n))))),
            Bind(m, ty)))
          )
        )
        val subgoal = InferGoal(c1, t)
        ResultGoalContext(
          List((r: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
             rc.results.get(subgoal) match {
              case Some(InferResult(ty1)) =>
                if(ty == ty1) rc.updateResults(g, InferResult(ty))
                else rc
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object InferForallInstantiation extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Inst(t1, t2)) =>
        val inferT1 = InferGoal(c, t1)
        val fcheckT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferT1) match {
            case Some(InferResult(PolyForallType(ty1, Bind(_, ty)))) =>
              CheckGoal(c, t2, ty1)
            case _ => ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((r: ResultGoalContext) => inferT1, fcheckT2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(inferT1), rc.results.get(fcheckT2(rc))) match {
              case (Some(InferResult(PolyForallType(ty1, Bind(_, ty)))), Some(CheckResult(true))) =>
                rc.updateResults(g, InferResult(ty))
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
    g match {
      case CheckGoal(c, IfThenElse(tc, t1, t2), ty) =>
        val c1 = c.bindFresh("_", EqualityType(tc, BoolLiteral(true)))
        val c2 = c.bindFresh("_", EqualityType(tc, BoolLiteral(false)))
        val checkCond = CheckGoal(c, tc, BoolType)
        val checkT1 = CheckGoal(c1, t1, ty)
        val checkT2 = CheckGoal(c2, t2, ty)
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
    g match {
      case CheckGoal(c, Match(t, t0, Bind(id, tn)), ty) =>
        val c1 = c.bindFresh("_", EqualityType(tn, NatLiteral(0)))
        val c2 = c.bindFresh("_", EqualityType(tn, NatLiteral(1))).bind(id, NatType)
        val checkCond = CheckGoal(c, t, NatType)
        val checkT0 = CheckGoal(c1, t0, ty)
        val checkTn = CheckGoal(c2, tn, ty)
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
    g match {
      case CheckGoal(c, EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), ty) =>
        val inferVar = InferGoal(c, t)
        val fcheckT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c1 = c.bindFresh("_", EqualityType(t, LeftTree(Var(id1)))).bind(id1, ty1)
              CheckGoal(c1, t1, ty)
            case _ => ErrorGoal(c)
          }
        }
        val fcheckT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(SumType(ty1, ty2))) =>
              val c2 = c.bindFresh("_", EqualityType(t, RightTree(Var(id2)))).bind(id2, ty2)
              CheckGoal(c2, t2, ty)
            case _ => ErrorGoal(c)
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
    g match {
      case CheckGoal(c, LetIn(None(), v, Bind(id, body)), ty) =>
        val gv = InferGoal(c, v)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(tyv)) =>
              val c1 = c.bind(id, tyv).bindFresh("_", EqualityType(Var(id), v))
              CheckGoal(c1, body, ty)
            case _ => ErrorGoal(c)
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
      case CheckGoal(c, LetIn(Some(tyv), v, Bind(id, body)), ty) =>
        val gv = CheckGoal(c, v, tyv)
        val c1 = c.bind(id, tyv).bindFresh("_", EqualityType(Var(id), v))
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


case object CheckForall extends Rule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, t, PolyForallType(tyid, Bind(id, ty))) =>
        val c1 = c.bind(id, tyid)
        val subgoal = CheckGoal(c1, t, ty)
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
    g match {
      case CheckGoal(c, t, PiType(ty1, Bind(_, ty2))) =>
        val id = Identifier(0, "_x")
        val c1 = c.bind(id, ty1)
        val subgoal = CheckGoal(c1, App(t, Var(id)), ty2)
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
    g match {
      case CheckGoal(c, t, SigmaType(ty1, Bind(id, ty2)))  =>
        val checkFirst = CheckGoal(c, First(t), ty1)
        val fcheckSecond = (rc: ResultGoalContext) => {
          rc.results.get(checkFirst) match {
            case Some(CheckResult(true)) =>
              val c1 = c.bind(id, ty1).bindFresh("_", EqualityType(Var(id), First(t)))
              CheckGoal(c1, Second(t), ty2)
            case _ => ErrorGoal(c)
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
    g match {
      case CheckGoal(c, LeftTree(t), SumType(ty1, ty2)) =>
        val subgoal = InferGoal(c, LeftTree(t))
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
    g match {
      case CheckGoal(c, RightTree(t), SumType(ty1, ty2)) =>
        val subgoal = InferGoal(c, RightTree(t))
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
    g match {
      case CheckGoal(c, t, RefinementType(ty, Bind(id, b)))  =>
        val checkTy = CheckGoal(c, t, ty)
        /*val fcheckSecond = (rc: ResultGoalContext) => {
          rc.results.get(checkTy) match {
            case Some(CheckResult(true)) =>
              val c1 = c.bind(id, ty1).bindFresh("_", EqualityType(Var(id), First(t)))
              CheckGoal(c1, Second(t), ty2)
            case _ => ErrorGoal(c)
          }
        }*/
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkTy), //fcheckSecond),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(checkTy) match { //, rc.results.get(fcheckSecond(rc))) match {
              case Some(CheckResult(true)) =>  //, Some(CheckResult(true))) =>
                rc.updateResults(g, CheckResult(true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}



object TypeChecker {
  val rule = InferBool.or(InferNat).or(InferApp).or(InferUnit).or(InferVar).or(InferLambda) || CheckLeft || CheckRefinement || CheckRight.or(CheckReflexive).or(NewErrorGoalRule).or(
    InferBinNatPrimitive).or(InferLet).or(InferIf).or(InferPair).or(InferFirst).or(InferSecond).or(InferMatch).or(
    CheckIf).or(CheckMatch).or(InferEitherMatch).or(InferError).or(InferBinBoolPrimitive) || InferUnBoolPrimitive || InferLeft || InferRight ||
    InferFix || InferForallInstantiation


  def infer(t: Tree) = {
    val g = InferGoal(Context(Map(), Set(), 0), t)
    val c = rule.repeat.apply(g)
    c.results.getOrElse(g, ErrorResult)
  }
}