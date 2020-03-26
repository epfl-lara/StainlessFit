package stainlessfit
package core
package typechecker

import core.trees._

import util.Utils._
import util.RunContext
import parser.FitParser

import Printer.asString

import Derivation._
import TypeOperators._
import ScalaDepSugar._

trait ScalaDepRules {

  implicit val rc: RunContext

  val InferLet1 = Rule("InferLet1", {
    case g @ InferGoal(c, e @ LetIn(None, v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet1")
      val c0 = c.incrementLevel
      val gv = InferGoal(c0, v)
      val fgb: List[Judgment] => Goal =
        {
          case InferJudgment(_, _, _, tyv) :: _ =>
            val c1 = c0.bind(id, tyv)
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c0, None)
        }
      Some((
        List(_ => gv, fgb),
        {
          case _ :: InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLet1", c, e, tyb))
          case _ =>
            emitErrorWithJudgment("InferLet1", g, None)
        }
      ))

    case _ => None
  })

  val InferLet2 = Rule("InferLet2", {
    case g @ InferGoal(c, e @ LetIn(Some(ty), v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet2")
      val c0 = c.incrementLevel
      val gv = CheckGoal(c0, v, ty)

      val c1 = c0.bind(id, ty)
      val g2: Goal = InferGoal(c1, body)

      Some((
        List(_ => gv, _ => g2),
        {
          case _ :: InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLet2", c, e, tyb))
          case _ =>
            emitErrorWithJudgment("InferLet2", g, None)
        }
      ))

    case _ => None
  })

  def widen(t: Tree): Tree = t match {
    case SingletonType(PiType(ty1, Bind(id, ty2)), f) =>
      PiType(ty1, Bind(id, SingletonType(ty2, App(f, Var(id)))))
    case _ => t
  }

  val InferApp1 = Rule("InferApp1", {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.debugs(g, "InferApp1")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          widen(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c,
              Some(s"Expected a Pi-type for ${asString(t1)}, found ${asString(ty)} instead")
            )
          }
        case _ =>
          ErrorGoal(c, None)
      }
      Some((
        List(_ => g1, fg2), {
          case  InferJudgment(_, _, _, ty) ::
                CheckJudgment(_, _, _, _) :: _ =>
            val PiType(_, Bind(x, tyb)) = widen(ty)
            (true, InferJudgment("InferApp1", c, e, tyb.replace(x, t2)))

          case _ =>
            emitErrorWithJudgment("InferApp1", g, None)
        }
      ))

    case _ => None
  })

  val InferVar1 = Rule("InferVar1", {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.debugs(g, "InferVar1")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None => emitErrorWithJudgment("InferVar1", g, Some(s"${asString(id)} is not in context"))
          case Some(ty) => (true, InferJudgment("InferVar1", c, Var(id), SingletonType(ty, Var(id))))
        }
      ))

    case g =>
      None
  })

  val InferCons = Rule("InferCons", {
    case g @ InferGoal(c, e @ `LCons`) =>
      TypeChecker.debugs(g, "InferCons")
      Some((List(), _ => (true, InferJudgment("InferCons", c, e, LConsType))))

    case g =>
      None
  })

  val CheckInfer = Rule("CheckInfer", {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.debugs(g, "CheckInfer")
      val c0 = c.incrementLevel
      val gInfer = InferGoal(c0, t)
      val fgsub: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty2) :: _ =>
          SubtypeGoal(c0, ty2, ty)
        case _ =>
          ErrorGoal(c, None)
      }
      Some((List(_ => gInfer, fgsub),
        {
          case InferJudgment(_, _, _, ty2) :: SubtypeJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckInfer", c, t, ty))
          case _ =>
            emitErrorWithJudgment("CheckInfer", g, None)
        }
      ))
    case g =>
      None
  })

  val SubReflexive = Rule("SubReflexive", {
    case g @ SubtypeGoal(c, ty1, ty2) if ty1 == ty2 =>
      TypeChecker.debugs(g, "SubReflexive")
      Some((List(), _ => (true, SubtypeJudgment("SubReflexive", c, ty1, ty2))))
    case g =>
      None
  })

  val SubTop = Rule("SubTop", {
    case g @ SubtypeGoal(c, ty, TopType) =>
      TypeChecker.debugs(g, "SubTop")
      Some((List(), _ => (true, SubtypeJudgment("SubTop", c, ty, TopType))))
    case g =>
      None
  })

  val SubSingletonLeft = Rule("SubSingletonLeft", {
    case g @ SubtypeGoal(c, ty @ SingletonType(ty1, _), ty2) if ty1 == ty2 =>
      TypeChecker.debugs(g, "SubSingletonLeft")
      Some((List(), _ => (true, SubtypeJudgment("SubSingletonLeft", c, ty, ty2))))
    case g =>
      None
  })

  val SubPi = Rule("SubArrow", {
    case g @ SubtypeGoal(c,
      tya @ PiType(tya1, Bind(ida, tya2)),
      tyb @ PiType(tyb1, Bind(idb, tyb2))) =>
      TypeChecker.debugs(g, "SubArrow")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tyb1, tya1)
      val g2 = SubtypeGoal(c0.bind(ida, tyb1), tya2, tyb2.replace(idb, ida))
      Some((List(_ => g1, _ => g2), _ => (true, SubtypeJudgment("SubArrow", c, tya, tyb))))
    case g =>
      None
  })

  val SubEval = Rule("SubEval", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(ty1, t1),
      tyb @ SingletonType(ty2, t2)) =>
      TypeChecker.debugs(g, "SubEval")

      val c0 = c.incrementLevel

      // val v1 = interpreter.Interpreter.evaluate(t1)
      // val v2 = interpreter.Interpreter.evaluate(t2)

      // if (v1 == v2)
        Some((List(_ => SubtypeGoal(c0, ty1, ty2)), {
          case SubtypeJudgment(_, _, _, _) :: _ =>
            (true, SubtypeJudgment("SubEval", c, tya, tyb))
          case _ =>
            emitErrorWithJudgment("SubEval", g, None)
        }))
      // else
      //   Some(
      //     List(), _ =>
      //     (false, ErrorJudgment("SubEval", g, Some(s"${asString(t1)} and ${asString(t2)} do not evaluate the same value (resp ${asString(v1)} and ${asString(v2)})")))
      //   )
    case g =>
      None
  })

  val InferListMatch = Rule("InferListMatch", {
    case g @ InferGoal(c, e @ ListMatch(t, t1, Bind(idHead, Bind(idTail, t2)))) =>
      TypeChecker.debugs(g, "InferListMatch")
      val c0 = c.incrementLevel
      val inferScrutinee = CheckGoal(c0, t, LList)

      val inferT1 = InferGoal(c0, t1)

      val c1 = c0.bind(idHead, TopType).bind(idTail, LList)
      val inferT2 = InferGoal(c1, t2)

      Some((
        List(_ => inferScrutinee, _ => inferT1, _ => inferT2), {
          case CheckJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty1) ::
            InferJudgment(_, _, _, ty2) :: _ =>
              (true, InferJudgment("InferListMatch", c, e,
                ListMatchType(t, ty1, Bind(idHead, Bind(idTail, ty2)))))

          case _ => emitErrorWithJudgment("InferListMatch", g, None)
        }
      ))

    case _ => None
  })

}
