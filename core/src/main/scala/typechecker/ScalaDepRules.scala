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
import interpreter.Interpreter

trait ScalaDepRules {

  implicit val rc: RunContext

  def withExistsIfFree(id: Identifier, tpe: Tree, t: Tree): Tree =
    if (id.isFreeIn(t)) ExistsType(tpe, Bind(id, t)) else t

  val InferNat1 = Rule("InferNat1", {
    case g @ InferGoal(c, e @ NatLiteral(n)) =>
      TypeChecker.debugs(g, "InferNat1")
      Some((List(), _ =>
        (true, InferJudgment("InferNat1", c, e, SingletonType(NatType, e)))))
    case g =>
      None
  })

  val InferLet1 = Rule("InferLet1", {
    case g @ InferGoal(c, e @ LetIn(None, v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet1")
      val c0 = c.incrementLevel
      val gv = InferGoal(c0, v)
      val fgb: List[Judgment] => Goal =
        {
          case InferJudgment(_, _, _, tyv) :: Nil =>
            val c1 = c0.bind(id, tyv)
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c0, None)
        }
      Some((
        List(_ => gv, fgb),
        {
          case InferJudgment(_, _, _, tyv) :: InferJudgment(_, _, _, tyb) :: Nil =>
            val ty = withExistsIfFree(id, tyv, tyb)
            (true, InferJudgment("InferLet1", c, e, ty))
          case _ =>
            emitErrorWithJudgment("InferLet1", g, None)
        }
      ))

    case _ => None
  })

  val InferLet2 = Rule("InferLet2", {
    case g @ InferGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet2")
      val c0 = c.incrementLevel
      val gv = CheckGoal(c0, v, tyv)

      val c1 = c0.bind(id, SingletonType(tyv, v))
      val g2: Goal = InferGoal(c1, body)

      Some((
        List(_ => gv, _ => g2),
        {
          case _ :: InferJudgment(_, _, _, tyb) :: _ =>
            val ty = withExistsIfFree(id, tyv, tyb)
            (true, InferJudgment("InferLet2", c, e, ty))
          case _ =>
            emitErrorWithJudgment("InferLet2", g, None)
        }
      ))

    case _ => None
  })

  val InferLambda1 = Rule("InferLambda1", {
    case g @ InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLambda1")
      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLambda1", c, e,
              SingletonType(PiType(ty1, Bind(id, tyb)), e)))
          case _ =>
            // Returning Top is sound but a bit misleading
            // (true, InferJudgment(c, e, TopType))
            emitErrorWithJudgment("InferLambda1", g, None)
        }
      ))

    case g =>
      None
  })

  def widen(t: Tree): Tree = t match {
    case SingletonType(PiType(ty1, Bind(id, ty2)), f) =>
      PiType(ty1, Bind(id, SingletonType(ty2, App(f, Var(id)))))
    case SingletonType(ty, f) =>
      widen(ty)
    case _ =>
      t
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
            case wty => ErrorGoal(c0,
              Some(s"Expected a Pi-type for ${asString(t1)}, found ${asString(ty)} instead (widened as ${asString(wty)}")
            )
          }
        case _ =>
          ErrorGoal(c0, None)
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

  val InferNil = Rule("InferNil", {
    case g @ InferGoal(c, e) if e == LNil() =>
      TypeChecker.debugs(g, "InferNil")
      Some((List(), _ => (true, InferJudgment("InferNil", c, e, LNilType))))

    case g =>
      None
  })

  val InferCons = Rule("InferCons", {
    case g @ InferGoal(c, e @ LCons(x, xs)) =>
      TypeChecker.debugs(g, "InferCons")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, x)
      val g2 = CheckGoal(c0, xs, LList)
      Some((List(_ => g1, _ => g2), {
        case InferJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: Nil =>
          (true, InferJudgment("InferCons", c, e, SingletonType(LList, e)))
        case _ =>
          emitErrorWithJudgment("InferCons", g, None)
      }))

    case g =>
      None
  })

  val InferChoose = Rule("InferChoose", {
    case g @ InferGoal(c, e @ Choose(ty)) =>
      TypeChecker.debugs(g, "InferChoose")
      val ety = PiType(Choose.PathType, Bind(Choose.unusedPath, ty))
      Some((List(), _ => (true, InferJudgment("InferChoose", c, e, ety))))

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
          NormalSubtypeGoal(c0, ty2, ty)
        case _ =>
          ErrorGoal(c0, None)
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

  def normalized(c: Context, ty: Tree): Tree = {
    def rec(
        c: Context,
        ty: Tree,
        linearExistsVars: Set[Identifier],
        inPositive: Boolean): Tree = {
      def recSimple(ty: Tree, inPositive: Boolean) =
        rec(c, ty, linearExistsVars, inPositive)
      ty match {
        case SingletonType(tyUnderlying, t) =>
          val tyUnderlyingN = recSimple(tyUnderlying, inPositive)
          t match {
            case Var(id) if linearExistsVars.contains(id) && inPositive =>
              // TODO: Check (or assert?) `tyUnderlyingN <: c.termVariables(id)`?
              tyUnderlyingN
            case _ =>
              val v = Interpreter.evaluateWithContext(c, t)
              SingletonType(tyUnderlyingN, v)
          }
        case ExistsType(ty1 @ SingletonType(_, _), Bind(id, ty2)) =>
          val ty1n = recSimple(ty1, inPositive)
          rec(c.bind(id, ty1n), ty2, linearExistsVars, inPositive)
        case ExistsType(ty1, Bind(id, ty2)) if Tree.linearVarsOf(ty2).contains(id) =>
          rec(c, ty2, linearExistsVars + id, inPositive)

        case ListMatchType(tScrut, tyNil, tyConsBind @ Bind(idHead, Bind(idTail, tyCons))) =>
          val tScrutN = Interpreter.evaluateWithContext(c, tScrut)
          tScrutN match {
            case LNil() =>
              recSimple(tyNil, inPositive)
            case LCons(tHead, tTail) =>
              val c0 = c
                .bind(idHead, SingletonType(TopType, tHead))
                .bind(idTail, SingletonType(LList, tTail))
              rec(c0, tyCons, linearExistsVars, inPositive)
            case _ =>
              ListMatchType(tScrutN, tyNil, tyConsBind)
          }

        case SumType(ty1, ty2) => SumType(recSimple(ty1, inPositive), recSimple(ty2, inPositive))
        case PiType(ty1, bind) => PiType(recSimple(ty1, false), recSimple(bind, inPositive))
        case SigmaType(ty1, bind) => SigmaType(recSimple(ty1, false), recSimple(bind, inPositive))
        case IntersectionType(ty1, bind) => IntersectionType(recSimple(ty1, false), recSimple(bind, inPositive))
        case RefinementType(ty1, bind) => RefinementType(recSimple(ty1, inPositive), recSimple(bind, inPositive))
        case RefinementByType(ty1, bind) => RefinementByType(recSimple(ty1, inPositive), recSimple(bind, inPositive))
        case RecType(n, bind) => ??? // RecType(recSimple(n), recSimple(bind))
        case PolyForallType(bind) => PolyForallType(recSimple(bind, inPositive))
        case Node(name, args) => Node(name, args.map(arg => recSimple(arg, inPositive)))
        case EqualityType(ty1, ty2) => ??? // EqualityType(recSimple(ty1), recSimple(ty2))
        case _ => ty
      }
    }
    rec(c, ty, Set.empty, true)
  }

  def NormalSubtypeGoal(c: Context, tya: Tree, tyb: Tree): SubtypeGoal =
    SubtypeGoal(c, normalized(c, tya), normalized(c, tyb))

  val SubReflexive = Rule("SubReflexive", {
    case g @ SubtypeGoal(c, ty1, ty2) if Tree.areEqual(ty1, ty2) =>
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
    case g @ SubtypeGoal(c, ty @ SingletonType(ty1, _), ty2) =>
      TypeChecker.debugs(g, "SubSingletonLeft")

      val subgoal = SubtypeGoal(c.incrementLevel, ty1, ty2)
      Some((List(_ => subgoal), {
        case SubtypeJudgment(_, _, _, _) :: _ =>
          (true, SubtypeJudgment("SubSingletonLeft", c, ty, ty2))
        case _ =>
          (false, ErrorJudgment("SubSingletonLeft", g, None))
      }))
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
      val g2 = NormalSubtypeGoal(c0.bind(ida, tyb1), tya2, tyb2.replace(idb, ida))
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubArrow", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubArrow", g, None)
      }))
    case g =>
      None
  })

  val SubListMatch = Rule("SubListMatch", {
    case g @ SubtypeGoal(c,
      tya @ ListMatchType(t, tyNil, Bind(idHead, Bind(idTail, tyCons))),
      tyb
    ) =>
      TypeChecker.debugs(g, "SubListMatch")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tyNil, tyb)
      val g2 = SubtypeGoal(c0.bind(idHead, TopType).bind(idTail, LList), tyCons, tyb)
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubListMatch", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubListMatch", g, None)
      }))

    case g =>
      None
  })

  val SubSingletonReflexive = Rule("SubSingletonReflexive", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(ty1, t1),
      tyb @ SingletonType(ty2, t2)) =>
      TypeChecker.debugs(g, "SubSingletonReflexive")

      val c0 = c.incrementLevel

      if (t1 == t2)
        Some((List(_ => SubtypeGoal(c0, tya, ty2)), {
          case SubtypeJudgment(_, _, _, _) :: _ =>
            (true, SubtypeJudgment("SubSingletonReflexive", c, tya, tyb))
          case _ =>
            emitErrorWithJudgment("SubSingletonReflexive", g, None)
        }))
      else
        Some((
          List(), _ =>
          (false, ErrorJudgment("SubSingletonReflexive", g, Some(s"${asString(t1)} and ${asString(t2)} are not the same")))
        ))
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

  val InferFixWithDefault = Rule("InferFixWithDefault", {
    case g @ InferGoal(c, e @ FixWithDefault(ty, t @ Bind(fIn, tBody), td)) =>
      TypeChecker.debugs(g, "InferFixWithDefault")

      val c0 = c.incrementLevel
      val c1 = c0.bind(fIn, ty)
      val g1 = CheckGoal(c1, tBody, ty)
      val g2 = CheckGoal(c0, td, ty)

      Some((
        List(_ => g1, _ => g2),
        _ =>
          (true, InferJudgment("InferFixWithDefault", c, e, SingletonType(ty, e)))))

    case _ => None
  })
}
