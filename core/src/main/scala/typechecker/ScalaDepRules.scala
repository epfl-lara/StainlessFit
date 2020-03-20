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

  val InferApp1 = Rule("InferApp1", {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.debugs(g, "InferApp1")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          ty match {
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
          case  InferJudgment(_, _, _, PiType(_, Bind(x, ty))) ::
                CheckJudgment(_, _, _, _) :: _ =>
            (true, InferJudgment("InferApp1", c, e, ty.replace(x, t2)))

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
          case None => emitErrorWithJudgment("InferVar1", g, Some(s"$id is not in context"))
          case Some(ty) => (true, InferJudgment("InferVar1", c, Var(id), SingletonType(ty, Var(id))))
        }
      ))

    case g =>
      None
  })

}
