package typer

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
        val frc = rule.apply(g)
        val rc = frc.merge(frc)
        if(rc.results.contains(g)) rc
        else rc.goals.foldLeft(rc) { case (rc, g) => apply(g(rc)) }
      }
    }
  }
}




case object NewInferBool extends NewRule {
  def apply(g: Goal): ResultGoalContext = {
    g match {
      case InferGoal(c, BoolLiteral(b)) =>
        ResultGoalContext(
          Nil(),
          Map(),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(BoolLiteral(b), BoolType)) }
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
          Map(),
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
          Map(),
          (rc: ResultGoalContext) => { rc.updateResults(g, InferResult(UnitLiteral, UnitType)) }
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
          rc.results(g1) match {
            case InferResult(_, PiType(ty2, ty)) => CheckGoal(c, t2, ty2)
            case _ => ErrorGoal(c)
          }
        }
        ResultGoalContext(
          List((rc: ResultGoalContext) => g1, fg2),
          Map(),
          (rc: ResultGoalContext) => {
            (rc.results(g1), rc.results(fg2(rc))) match {
              case (InferResult(_, PiType(_, ty)), CheckResult(_, _, true)) => rc.updateResults(g, InferResult(App(t1, t2), ty))
              case _ => rc
            }
          }
        )
      case _ => errorContext
    }
  }
}

trait Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result))

  val returnError: (List[Goal], (List[Result] => Result)) =
    (List(), ((gs: List[Result]) => ErrorResult))

  def or(other: Rule): Rule = Rule.or(this, other)
  def repeat(): Rule = Rule.repeat(this)
  //def compose(other: Rule): Rule = Rule.compose(this, other)
}



object Rule {
  def or(rule1: Rule, rule2: Rule): Rule = {
    new Rule {
      def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
        val (goals1, merge1): (List[Goal], (List[Result] => Result))  = rule1.apply(g)
        val (goals2, merge2): (List[Goal], (List[Result] => Result)) = rule2.apply(g)
        (
          goals1 ++ goals2,
          ((results: List[Result]) => {
            val r1 = merge1(results.take(goals1.size))
            if(r1 != ErrorResult) r1
            else merge2(results.drop(goals1.size))
          })
        )
      }
    }
  }

  /*def zipWithIndex[T](l: List[T]): List[(T, Int)] = {
    def f(l: List[T], i: Int): List[(T, Int)] = {
      l match {
        case Nil() => Nil()
        case Cons(x, l) => Cons((x, i), f(l, i + 1))
      }
    }
    f(l, 0)
  }

  def zipWithCumulatedSize[T](l: List[List[T]]): List[(List[T], BigInt)] = {
    def f(l: List[List[T]], i: BigInt): List[(List[T], BigInt)] = {
      l match {
        case Nil() => Nil()
        case Cons(x, l) => Cons((x, i), f(l, i + x.size))
      }
    }
    f(l, BigInt(0))
  }

  def compose(rule1: Rule, rule2: Rule) = {
    new Rule {
      def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
        val (goals2, merge2): (List[Goal], (List[Result] => Result)) = rule2.apply(g)
        val listPair = goals2.map(rule2.apply(_))
        val goals: List[(List[Goal], BigInt)] = zipWithCumulatedSize(listPair.map { case (g, m) => g })
        val merges = zipWithIndex(listPair.map { case (g, m) => m })
        (
          goals.flatMap { case (x, s) => x },
          ((results: List[Result]) => {
            merge2(
              merges.map { case (m, i) => m(results.drop(goals(i)._2).take(goals(i)._1.size)) }
            )
          })
        )
      }
    }
  }*/

  def repeat(rule: Rule): Rule = {
    new Rule {
      def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
        rule.apply(g) match {
          case (Nil(), merge) => (Nil(), merge)
          case (gs, merge) =>
            val results = gs.map { g =>
              val (gs, merge): (List[Goal], (List[Result] => Result)) = apply(g)
              merge(Nil())
            }
            (Nil(), ((r: List[Result]) =>  merge(results)))
        }
      }
    }
  }
}

case object InferVar extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Var(id)) =>
        c.getTypeOf(id) match {
          case Some(ty) => (List(), ((gs: List[Result]) => InferResult(Var(id), ty)))
          case None() => returnError
        }
      case _ => returnError
    }
  }
}

case object InferBool extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, BoolLiteral(b)) =>
        (List(), ((gs: List[Result]) => InferResult(BoolLiteral(b), BoolType)))
      case _ => returnError
    }
  }
}

case object InferUnit extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, UnitLiteral) =>
        (List(), ((gs: List[Result]) => InferResult(UnitLiteral, UnitType)))
      case _ => returnError
    }
  }
}

case object InferNat extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, NatLiteral(n)) =>
        (List(), ((gs: List[Result]) => InferResult(NatLiteral(n), NatType)))
      case _ => returnError
    }
  }
}

case object InferIf extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, IfThenElse(tc, t1, t2)) =>
        val c1 = c.bindFresh("_", EqualityType(tc, BoolLiteral(true)))
        val c2 = c.bindFresh("_", EqualityType(tc, BoolLiteral(false)))
        val checkCond = CheckGoal(c, tc, BoolType)
        val inferT1 = InferGoal(c1, t1)
        val inferT2 = InferGoal(c2, t2)
        (
          List(checkCond, inferT1, inferT2),
          (gs: List[Result]) => {
            gs match {
              case Cons(CheckResult(tc, tyc, true), Cons(InferResult(t1, tyt), Cons(InferResult(t2, tyf), Nil()))) =>
                if(tyt == tyf) InferResult(IfThenElse(tc, t1, t2), tyt)
                else ErrorResult
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferLeft extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, LeftTree(t)) =>
        (
          List(InferGoal(c, t)),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(t, SumType(ty1, ty2)), Nil()) =>
                InferResult(LeftTree(t), ty1)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferRight extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, RightTree(t)) =>
        (
          List(InferGoal(c, t)),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(t, SumType(ty1, ty2)), Nil()) =>
                InferResult(RightTree(t), ty2)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object CheckReflexive extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case CheckGoal(c, t, ty) =>
        (
          List(InferGoal(c, t)),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(t, ty1), Nil()) =>
                CheckResult(t, ty1, true)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferMatch extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Match(t, t0, Bind(Some(id), tn))) =>
        val c1 = c.bindFresh("_", EqualityType(tn, NatLiteral(0)))
        val c2 = c.bindFresh("_", EqualityType(tn, NatLiteral(1))).bind(id, NatType)   // Use bindfresh instead and update tn
        val checkCond = CheckGoal(c, t, NatType)
        val inferT1 = InferGoal(c1, t0)
        val inferT2 = InferGoal(c2, tn)
        (
          List(checkCond, inferT1, inferT2),
          (gs: List[Result]) => {
            gs match {
              case Cons(CheckResult(tc, tyc, b), Cons(InferResult(t0, ty0), Cons(InferResult(n, tyn), Nil()))) =>
                if(b && ty0 == tyn) InferResult(Match(t, t0, Bind(Some(id), tn)), ty0)
                else ErrorResult
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferLambda extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Lambda(Some(ty1), Bind(Some(id), body))) =>
        val c1 = c.bind(id, ty1)
        val inferBody = InferGoal(c1, body)
        (
          List(inferBody),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(body, bodyTy), Nil()) =>
                InferResult(
                  Lambda(Some(ty1), Bind(Some(id), body)),
                  PiType(ty1, bodyTy)
                  )
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferPair extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Pair(t1, t2))  =>
        val inferFirst = InferGoal(c, t1)
        val inferSecond = InferGoal(c, t2)
        (
          List(inferFirst, inferSecond),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(_, ty1), Cons(InferResult(_, ty2), Nil())) =>
                InferResult(Pair(t1, t2), SigmaType(ty1, Bind(Some(Identifier(Some(0), "x")), ty2)))
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferFirst extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, First(t))  =>
        val inferT = InferGoal(c, t)
        (
          List(inferT),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(_, SigmaType(ty1, _)), Nil()) =>
                InferResult(First(t), ty1)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object InferSecond extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Second(t))  =>
        val inferT = InferGoal(c, t)
        (
          List(inferT),
          (gs: List[Result]) => {
            gs match {
              case Cons(InferResult(_, SigmaType(_, Bind(_, ty2))), Nil()) =>
                InferResult(First(t), ty2)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}




case object InferBinNatPrimitive extends Rule {

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

  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, Primitive(op, Cons(n1, Cons(n2, Nil())))) if isNatBinOp(op) =>
        val checkN1 = CheckGoal(c, n1, NatType)
        val checkN2 = CheckGoal(c, n2, NatType)
        (
          List(checkN1, checkN2),
          (gs: List[Result]) => {
            gs match {
              case Cons(CheckResult(_, _, true), Cons(CheckResult(_, _, true), Nil())) =>
                val retType = if(isNatToBoolBinOp(op)) BoolType else NatType
                InferResult(Primitive(op, Cons(n1, Cons(n2, Nil()))), retType)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

/*case object InferLet extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case InferGoal(c, LetIn(_, v, Bind(Some(id), t))) =>
        val inferVal = InferGoal(c, v)

      case c => returnError
    }
  }
}*/





case object CheckIf extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    g match {
      case CheckGoal(c, IfThenElse(tc, t1, t2), ty) =>
        val c1 = c.bindFresh("_", EqualityType(tc, BoolLiteral(true)))
        val c2 = c.bindFresh("_", EqualityType(tc, BoolLiteral(false)))
        val checkCond = CheckGoal(c, tc, BoolType)
        val checkT1 = CheckGoal(c1, t1, ty)
        val checkT2 = CheckGoal(c2, t2, ty)
        (
          List(checkCond, checkT1, checkT2),
          (gs: List[Result]) => {
            gs match {
              case Cons(CheckResult(tc, tyc, true), Cons(CheckResult(t1, tyt, true), Cons(CheckResult(t2, tyf, true), Nil()))) =>
                CheckResult(IfThenElse(tc, t1, t2), ty, true)
              case _ => ErrorResult
            }
          }
        )
      case _ => returnError
    }
  }
}

case object ErrorGoalRule extends Rule {
  def apply(g: Goal): (List[Goal], (List[Result] => Result)) = {
    returnError
  }
}

object TypeChecker {

  val rule = InferUnit.or(InferBool).or(InferIf).or(CheckReflexive).or(InferNat).or(InferVar).or(InferMatch).or(InferLambda).or(InferBinNatPrimitive)

  def infer(t: Tree): Result = {
    val (goals, merge):(List[Goal], (List[Result] => Result)) = rule.repeat.apply(InferGoal(Context(Map(), Set(), 0), t))
    merge(Nil())
  }

  def newInfer(t: Tree) = {
    val g = InferGoal(Context(Map(), Set(), 0), t)
    val c = NewInferBool.or(NewInferNat).apply(g)
    c.merge(c).results.getOrElse(g, ErrorResult)
  }
}