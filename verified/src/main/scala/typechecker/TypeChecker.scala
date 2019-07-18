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
  def bindFresh(s: String, t: Tree) = bind(Identifier(Some(n), s), t).copy(n = n+1)

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

case class InferResult(t: Tree, ty: Tree) extends Result
case class CheckResult(t: Tree, ty: Tree, b: Boolean)  extends Result
case class SynthesizeResult(t: Tree, ty: Tree)  extends Result
case object ErrorResult extends Result


case class ResultGoalContext(
  val goals: List[ResultGoalContext => Goal],
  val results: Map[Goal, Result],
  val merge: ResultGoalContext => ResultGoalContext
) {
  def updateResults(goal: Goal, result: Result) = {
    result match {
      case ErrorResult => this
      case _ => copy(results = results.updated(goal, result))
    }
  }
}

trait NewRule {
  def apply(g: Goal): ResultGoalContext

  val errorContext: ResultGoalContext =
    ResultGoalContext(
      Nil(),
      Map(),
      (rc: ResultGoalContext) => rc
    )

  def or(other: NewRule): NewRule = NewRule.or(this, other)
  def repeat: NewRule = NewRule.repeat(this)
}



object NewRule {
  def or(rule1: NewRule, rule2: NewRule): NewRule = {
    new NewRule {
      def apply(g: Goal): ResultGoalContext = {
        val rc1: ResultGoalContext = rule1.apply(g)
        val rc2: ResultGoalContext = rule2.apply(g)
        ResultGoalContext(
          rc1.goals ++ rc2.goals,
          rc1.results ++ rc2.results, // Should merge the two results rc1.mergeResults(rc2)
          (rc: ResultGoalContext) => {
            val newRC1 = rc1.merge(rc)
            val newRC2 = rc2.merge(rc)
            ResultGoalContext(newRC1.goals ++ newRC2.goals, newRC1.results ++ newRC2.results, (rc: ResultGoalContext) => rc)
          }
        )
      }
    }
  }

  def repeat(rule: NewRule): NewRule = {
    new NewRule {
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

case object NewErrorGoalRule extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    errorContext
  }
}


case object NewInferBool extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, BoolLiteral(b)) =>
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(BoolLiteral(b), BoolType)),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(BoolLiteral(b), BoolType)) }
        )
      case _ => errorContext
    }
  }
}

case object NewCheckReflexive extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, t, ty) =>
        val gInfer = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gInfer),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gInfer) match {
              case Some(InferResult(t, ty1)) =>
                rc.updateResults(
                  g,
                  CheckResult(t, ty1, ty1 == ty)
                )
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferNat extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, NatLiteral(n)) =>
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(NatLiteral(n), NatType)),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(NatLiteral(n), NatType)) }
        )
      case _ => errorContext
    }
  }
}

case object NewInferUnit extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, UnitLiteral) =>
        ResultGoalContext(
          Nil(),
          Map(g -> InferResult(UnitLiteral, UnitType)),
          (rc: ResultGoalContext) => rc.updateResults(g, InferResult(UnitLiteral, UnitType))
        )
      case _ => errorContext
    }
  }
}

case object NewInferVar extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Var(id)) =>
        ResultGoalContext(
          Nil(),
          c.getTypeOf(id) match {
            case Some(ty) => Map(g -> InferResult(Var(id), ty))
            case None() => Map()
          },
          c.getTypeOf(id) match {
            case Some(ty) => (rc: ResultGoalContext) => rc.updateResults(g, InferResult(Var(id), ty))
            case None() => (rc: ResultGoalContext) => rc
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferApp extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, App(t1, t2)) =>
        val g1 = InferGoal(c, t1)
        val fg2 = (rc: ResultGoalContext) => {
          rc.results.get(g1) match {
            case Some(InferResult(_, PiType(ty2, ty))) => CheckGoal(c, t2, ty2)
            case _ =>
              ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => g1, fg2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(g1), rc.results.get(fg2(rc))) match {
              case (Some(InferResult(_, PiType(_, ty))), Some(CheckResult(_, _, true))) => rc.updateResults(g, InferResult(App(t1, t2), ty))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferLambda extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Lambda(Some(ty1), Bind(Some(id), body))) =>
        val c1 = c.bind(id, ty1)
        val gb = InferGoal(c1, body)
        ResultGoalContext(
          List((rc: ResultGoalContext) => gb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(gb) match {
              case Some(InferResult(body, bodyTy)) =>
                rc.updateResults(
                  g,
                  InferResult(Lambda(Some(ty1), Bind(Some(id), body)), PiType(ty1, bodyTy))
                )
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferBinNatPrimitive extends NewRule {

  def isNatToNatBinOp(op: Operator): Boolean = {
    op match {
      case Plus => true
      case Minus => true
      case Mul => true
      case Div => true
      case _ => false
    }
  }

  def isNatToBoolBinOp(op: Operator): Boolean = {
    op match {
      case Eq => true
      case Neq => true
      case Lteq => true
      case Gteq => true
      case Lt => true
      case Gt => true
      case _ => false
    }
  }

  def isNatBinOp(op: Operator): Boolean = {
    isNatToNatBinOp(op) || isNatToBoolBinOp(op)
  }

  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Primitive(op, Cons(n1, Cons(n2, Nil())))) if isNatBinOp(op) =>
        val checkN1 = CheckGoal(c, n1, NatType)
        val checkN2 = CheckGoal(c, n2, NatType)
        ResultGoalContext(
          List((rc: ResultGoalContext) => checkN1, (rc: ResultGoalContext) => checkN2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results.get(checkN1), rc.results.get(checkN2)) match {
              case (Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true))) =>
                val retType = if(isNatToBoolBinOp(op)) BoolType else NatType
                rc.updateResults(g, InferResult(Primitive(op, Cons(n1, Cons(n2, Nil()))), retType))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferLet extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, LetIn(tp, v, Bind(Some(id), body))) =>
        val gv = InferGoal(c, v)
        val fgb = (rc: ResultGoalContext) => {
          rc.results.get(gv) match {
            case Some(InferResult(_, tyv)) =>
              val c1 = c.bind(id, tyv)
              InferGoal(c1, body)
            case _ => ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => gv, fgb),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(fgb(rc)) match {
              case Some(InferResult(_, ty)) =>
                rc.updateResults(g, InferResult(LetIn(tp, v, Bind(Some(id), body)), ty))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferIf extends NewRule {
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
              case (Some(CheckResult(_, _, true)), Some(InferResult(_, ty1)), Some(InferResult(_, ty2))) =>
                if(ty1 == ty2) rc.updateResults(g, InferResult(IfThenElse(tc, t1, t2), ty1))
                else rc
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferLeft extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, LeftTree(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(_, SumType(ty1, ty2))) => rc.updateResults(g, InferResult(LeftTree(t), ty1))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferRight extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, LeftTree(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(_, SumType(ty1, ty2))) => rc.updateResults(g, InferResult(RightTree(t), ty2))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferPair extends NewRule {
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
              case (Some(InferResult(_, ty1)), Some(InferResult(_, ty2))) =>
                rc.updateResults(g, InferResult(Pair(t1, t2), SigmaType(ty1, Bind(Some(Identifier(Some(0), "x")), ty2))))
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferFirst extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, First(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(_, SigmaType(ty1, ty2))) => rc.updateResults(g, InferResult(First(t), ty1))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferSecond extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Second(t)) =>
        val subgoal = InferGoal(c, t)
        ResultGoalContext(
          List((rc: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
            rc.results.get(subgoal) match {
              case Some(InferResult(_, SigmaType(ty1, ty2))) => rc.updateResults(g, InferResult(Second(t), ty2))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}


case object NewInferMatch extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, Match(t, t0, Bind(Some(id), tn))) =>
        val c1 = c.bindFresh("_", EqualityType(tn, NatLiteral(0)))
        val c2 = c.bindFresh("_", EqualityType(tn, NatLiteral(1))).bind(id, NatType)
        val checkCond = CheckGoal(c, t, NatType)
        val inferT0 = InferGoal(c1, t0)
        val inferTn = InferGoal(c2, tn)
        ResultGoalContext(
          List((r: ResultGoalContext) => checkCond, (r: ResultGoalContext) => inferT0, (r: ResultGoalContext) => inferTn),
          Map(),
          (rc: ResultGoalContext) => {
             (rc.results.get(checkCond), rc.results.get(inferT0), rc.results.get(inferTn)) match {
              case (Some(CheckResult(_, _, true)), Some(InferResult(_, ty0)), Some(InferResult(_, tyn))) =>
                if(ty0 == tyn) rc.updateResults(g, InferResult(Match(t, t0, Bind(Some(id), tn)), ty0))
                else rc
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewInferEitherMatch extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, EitherMatch(t, Bind(Some(id1), t1), Bind(Some(id2), t2))) =>
        val inferVar = InferGoal(c, t)
        val finferT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(_, SumType(ty1, ty2))) =>
              val c1 = c.bindFresh("_", EqualityType(t, LeftTree(Var(id1)))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c)
          }
        }
        val finferT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(_, SumType(ty1, ty2))) =>
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
              case (Some(InferResult(_, ty1)), Some(InferResult(_, ty2))) =>
                if(ty1 == ty2) rc.updateResults(g, InferResult(EitherMatch(t, Bind(Some(id1), t1), Bind(Some(id2), t2)), ty1))
                else rc
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}





case object NewCheckIf extends NewRule {
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
              case (Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true))) =>
                rc.updateResults(g, CheckResult(IfThenElse(tc, t1, t2), ty, true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewCheckMatch extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, Match(t, t0, Bind(Some(id), tn)), ty) =>
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
              case (Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true))) =>
                rc.updateResults(g, CheckResult(Match(t, t0, Bind(Some(id), tn)), ty, true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewCheckEitherMatch extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, EitherMatch(t, Bind(Some(id1), t1), Bind(Some(id2), t2)), ty) =>
        val inferVar = InferGoal(c, t)
        val fcheckT1 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(_, SumType(ty1, ty2))) =>
              val c1 = c.bindFresh("_", EqualityType(t, LeftTree(Var(id1)))).bind(id1, ty1)
              CheckGoal(c1, t1, ty)
            case _ => ErrorGoal(c)
          }
        }
        val fcheckT2 = (rc: ResultGoalContext) => {
          rc.results.get(inferVar) match {
            case Some(InferResult(_, SumType(ty1, ty2))) =>
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
              case (Some(CheckResult(_, _, true)), Some(CheckResult(_, _, true))) =>
                rc.updateResults(g, CheckResult(EitherMatch(t, Bind(Some(id1), t1), Bind(Some(id2), t2)), ty, true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewCheckPi extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, t, PiType(ty1, ty2)) =>
        val id = Identifier(Some(0), "_x")
        val c1 = c.bind(id, ty1)
        val subgoal = CheckGoal(c1, App(t, Var(id)), ty2)
        ResultGoalContext(
          List((r: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
             rc.results.get(subgoal) match {
              case Some(CheckResult(_, _, true)) =>
                rc.updateResults(g, CheckResult(t, PiType(ty1, ty2), true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

case object NewCheckForall extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case CheckGoal(c, t, PolyForallType(tyid, Bind(Some(id), ty))) =>
        val c1 = c.bind(id, tyid)
        val subgoal = CheckGoal(c1, t, ty)
        ResultGoalContext(
          List((r: ResultGoalContext) => subgoal),
          Map(),
          (rc: ResultGoalContext) => {
             rc.results.get(subgoal) match {
              case Some(CheckResult(_, _, true)) =>
                rc.updateResults(g, CheckResult(t, PolyForallType(tyid, Bind(Some(id), ty)), true))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}




object TypeChecker {

  def newInfer(t: Tree) = {

    val rule = NewInferBool.or(NewInferNat).or(NewInferApp).or(NewInferUnit).or(NewInferVar).or(NewInferLambda).or(NewCheckReflexive).or(NewErrorGoalRule).or(
               NewInferBinNatPrimitive).or(NewInferLet).or(NewInferIf).or(NewInferPair).or(NewInferFirst).or(NewInferSecond).or(NewInferMatch).or(
                NewCheckIf).or(NewCheckMatch).or(NewInferEitherMatch)
    val g = InferGoal(Context(Map(), Set(), 0), t)
    val c = rule.repeat.apply(g)
    c.results.getOrElse(g, InferResult(UnitLiteral, UnitLiteral))
  }
}