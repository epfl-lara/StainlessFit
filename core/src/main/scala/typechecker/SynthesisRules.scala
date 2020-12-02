/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import core.trees._

import util.RunContext
import util.Utils._

import Derivation._

trait SynthesisRules {

  implicit val rc: RunContext

  val SynthesisUnit = Rule("SynthesisUnit", {
    case g @ SynthesisGoal(c, UnitType) =>
      Some((List(), _ => (true, SynthesisJudgment("SynthesisUnit", c, UnitType, UnitLiteral))))
    case g =>
      None
  })

  val SynthesisBool = Rule("SynthesisBool", {
    case g @ SynthesisGoal(c, BoolType) =>
      Some((List(), _ => (true, SynthesisJudgment("SynthesisBool", c, BoolType, BooleanLiteral(true)))))
    case g =>
      None
  })

  val SynthesisNat = Rule("SynthesisNat", {
    case g @ SynthesisGoal(c, NatType) =>
      Some((List(), _ => (true, SynthesisJudgment("SynthesisNat", c, NatType, NatLiteral(0)))))
    case g =>
      None
  })

  val SynthesisVar = Rule("SynthesisVar", {
    case g @ SynthesisGoal(c, tp) =>
      c.getVarOfType(tp).map(v =>
        (List(), _ => (true, SynthesisJudgment("SynthesisVar", c, NatType, Var(v))))
      )
    case g =>
      None
  })

  val SynthesisPi = Rule("SynthesisPi", {
    case g @ SynthesisGoal(c, tp @ PiType(tyX, Bind(x, ty))) =>
      val c1 = c.bind(x, tyX).incrementLevel
      val gb = SynthesisGoal(c, ty)
      Some((
        List(_ => gb),
        {
          case SynthesisJudgment(_, _, _, t) :: _ =>
            (true, SynthesisJudgment("SynthesisPi", c, tp, Lambda(Some(tyX), Bind(x, t))))
          case _ =>
            emitErrorWithJudgment("SynthesisPi", g, None)
        }
      ))
    case _ => None
  })

  val SynthesisSigma = Rule("SynthesisSigma", {
    case g @ SynthesisGoal(c, tp @ SigmaType(ty1, Bind(id, ty2))) =>
      val g1 = SynthesisGoal(c.incrementLevel, ty1)
      val fg2: List[Judgment] => Goal = {
        case SynthesisJudgment(_, _, _, t1) :: _ =>
          val c1 = c.incrementLevel.bind(id, t1)
          SynthesisGoal(c1, ty2)
        case _ =>
          ErrorGoal(c, None)
      }
      Some((
        List(_ => g1, fg2),
        {
          case SynthesisJudgment(_, _, _, t1) :: SynthesisJudgment(_, _, _, t2) :: _ =>
            (true, SynthesisJudgment("SynthesisSigma", c, tp, Pair(t1, t2)))
          case _ =>
            emitErrorWithJudgment("SynthesisSigma", g, None)
        }
      ))
    case _ => None
  })

  val SynthesisSum = Rule("SynthesisSum", {
    case g @ SynthesisGoal(c, tp @ SumType(ty1, ty2)) =>
      val g1 = SynthesisGoal(c.incrementLevel, ty1)
      val g2 = SynthesisGoal(c.incrementLevel, ty1)
      Some((
        List(_ => g1, _ => g2),
        {
          case SynthesisJudgment(_, _, _, t1) :: _ =>
            (true, SynthesisJudgment("SynthesisSum", c, tp, LeftTree(t1)))
          case _ :: SynthesisJudgment(_, _, _, t2) :: _ =>
            (true, SynthesisJudgment("SynthesisSum", c, tp, RightTree(t2)))
          case _ =>
            emitErrorWithJudgment("SynthesisSum", g, None)
        }
      ))
    case _ => None
  })
}
