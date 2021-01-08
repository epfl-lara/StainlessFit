/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import core.trees._

import util.Utils._
import util.RunContext
import parser.FitParser

import Printer.asString

import Derivation._
import TypeOperators._
import SDepSugar._
import interpreter.Interpreter

trait SDepRules { self: SDep =>
  // TODO: Add freshen whenever we bind

  def withExistsIfFree(id: Identifier, tpe: Tree, t: Tree): Tree =
    if (id.isFreeIn(t)) ExistsType(tpe, Bind(id, t)) else t

  val InferUnit1 = Rule("InferUnit1", {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.debugs(g, "InferUnit1")
      Some((List(), _ => (true, InferJudgment("InferUnit1", c, UnitLiteral, SingletonType(UnitType, UnitLiteral)))))
    case g =>
      None
  })

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
            val (c1, bodyF) = c0.bindAndFreshen(id, tyv, body)
            InferGoal(c1, bodyF)
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

      val (c1, bodyF) = c0.bindAndFreshen(id, SingletonType(tyv, v), body)
      val g2: Goal = InferGoal(c1, bodyF)

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
      val (c1, bodyF) = c.incrementLevel.bindAndFreshen(id, ty1, body)
      val gb = InferGoal(c1, bodyF)
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

  val InferSolverVar = Rule("InferSolverVar", {
    case g @ InferGoal(c, Var(id)) if isTarget(id) =>
      TypeChecker.debugs(g, "InferSolverVar")
      Some((List(), _ =>
        (true, InferJudgment("InferSolverVar", c, Var(id), SingletonType(lookupTarget(id), Var(id))))
      ))

    case g =>
      None
  })

  val InferNormalVar = Rule("InferNormalVar", {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.debugs(g, "InferNormalVar")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None => emitErrorWithJudgment("InferNormalVar", g, Some(s"${asString(id)} is not in context"))
          case Some(ty) => (true, InferJudgment("InferNormalVar", c, Var(id), SingletonType(ty, Var(id))))
        }
      ))

    case g =>
      None
  })

  val InferSucc = Rule("InferSucc", {
    case g @ InferGoal(c, e @ Succ(t)) =>
      TypeChecker.debugs(g, "InferSucc")
      val g1 = InferGoal(c.incrementLevel, t)
      Some((List(_ => g1),
        {
          case InferJudgment(_, _, _, ty) :: Nil =>
            (true, InferJudgment("InferSucc", c, e, SingletonType(NatType, e)))
          case _ =>
            emitErrorWithJudgment("InferSucc", g, None)
        }
      ))
    case g =>
      None
  })

  val InferPair1 = Rule("InferPair1", {
    case g @ InferGoal(c, e @ Pair(t1, t2)) =>
      TypeChecker.debugs(g, "InferPair1")
      val inferFirst = InferGoal(c.incrementLevel, t1)
      val inferSecond = InferGoal(c.incrementLevel, t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case InferJudgment(_, _, _, ty1) :: InferJudgment(_, _, _, ty2) :: Nil =>
            val inferredType = SigmaType(ty1, Bind(Identifier.fresh("X"), ty2))
            (true, InferJudgment("InferPair1", c, e, SingletonType(inferredType, e)))
          case _ =>
            emitErrorWithJudgment("InferPair1", g, None)
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
    case g @ InferGoal(c, e @ LCons(tHead, tTail)) =>
      TypeChecker.debugs(g, "InferCons")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, tHead)
      val g2 = InferGoal(c0, tTail)
      val g3: List[Judgment] => Goal = {
        case _ :: InferJudgment(_, _, _, tyTail) :: Nil =>
          NormalizedSubtypeGoal(c0, tyTail, LList)
        case _ =>
          ErrorGoal(c0, None)
      }
      Some((List(_ => g1, _ => g2, g3), {
        case InferJudgment(_, _, _, tyHead) :: InferJudgment(_, _, _, tyTail) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, InferJudgment("InferCons", c, e, SingletonType(LConsType(tyHead, tyTail), e)))
        case _ =>
          emitErrorWithJudgment("InferCons", g, None)
      }))

    case g =>
      None
  })

  val InferChoose = Rule("InferChoose", {
    case g @ InferGoal(c, e @ ChooseWithPath(ty, tPath)) =>
      TypeChecker.debugs(g, "InferChoose")
      Some((List(), _ => (true, InferJudgment("InferChoose", c, e, SingletonType(ty, e)))))

    case g =>
      None
  })

  val InferAscribe = Rule("InferAscribe", {
    case g @ InferGoal(c, e @ Ascribe(t, ty)) =>
      TypeChecker.debugs(g, "InferAscribe")
      val c0 = c.incrementLevel
      val gc = CheckGoal(c0, t, ty)

      Some((
        List(_ => gc),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, InferJudgment("InferAscribe", c, e, ty))
          case _ =>
            emitErrorWithJudgment("InferAscribe", g, None)
        }
      ))

    case _ => None
  })

  val CheckInfer = Rule("CheckInfer", {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.debugs(g, "CheckInfer")
      val c0 = c.incrementLevel
      val gInfer = InferGoal(c0, t)
      val fgsub: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty2) :: _ =>
          NormalizedSubtypeGoal(c0, ty2, ty)
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

  val ContextSanity = {
    val MaxLevel = 80

    def error(g: Goal, msg: String) =
      Some((List(), (_: List[Judgment]) =>
        emitErrorWithJudgment("ContextSanity", g, Some(msg))))

    def hasBadBinding(c: Context, e: Tree)(implicit rc: RunContext): Boolean = {
      var sane = true
      e.preMap {
        case Bind(id, _) if c.termVariables.contains(id) =>
          sane = false
          None
        case _ => None
      }
      !sane
    }
    def hasEscapedBinding(c: Context, e: Tree): Boolean = {
      (e.freeVars -- c.termVariables.keySet -- targetVars).nonEmpty
    }
    def checkBindings(g: Goal, t: Tree) =
      if (hasBadBinding(g.c, t)) error(g, "Has a bad binding")
      else if (hasEscapedBinding(g.c, t)) error(g, "Has an escaped binding")
      else None

    def checkDepth(g: Goal) =
      if (g.c.level > MaxLevel) error(g, s"Exceeds the maximum level ($MaxLevel)") else None

    Rule("ContextSanity", {
      case g @ InferGoal(c, t) =>
        checkDepth(g).orElse(checkBindings(g, t))
      case g @ NormalizationGoal(c, ty) =>
        checkDepth(g).orElse(checkBindings(g, ty))
      case g =>
        checkDepth(g)
    })
  }

  val NormSingleton = Rule("NormSingleton", {
    case g @ NormalizationGoal(c, ty @ SingletonType(tyUnderlying, t)) =>
      TypeChecker.debugs(g, "NormSingleton")
      val c0 = c.incrementLevel
      Interpreter.shouldRetype = false // FIXME: Hack
      val v = Interpreter.evaluateWithContext(interpreterContext(c), t)

      // Re-type if we performed any delta reductions during evaluation:
      if (Interpreter.shouldRetype) {
        val g1 = InferGoal(c0, v)
        Some((List(_ => g1), {
          case InferJudgment(_, _, _, tyV) :: Nil =>
            (true, NormalizationJudgment("NormSingleton", c, ty, tyV))
          case _ =>
            emitErrorWithJudgment("NormSingleton", g, None)
        }))
        // TODO: Also normalize type after reinferring it?
        // val fg2: List[Judgment] => Goal = {
        //   case InferJudgment(_, _, _, tyV) :: Nil =>
        //     NormalizationGoal(c0, tyV)
        //   case _ =>
        //     ErrorGoal(c0, Some(s"Expected normalized type"))
        // }
        // Some((List(_ => g1, fg2), {
        //   case InferJudgment(_, _, _, _)  :: NormalizationJudgment(_, _, _, tyVN) :: Nil =>
        //     (true, NormalizationJudgment("NormSingleton", c, ty, tyVN))
        //   case _ =>
        //     emitErrorWithJudgment("NormSingleton", g, None)
        // }))
      } else {
        val g1 = NormalizationGoal(c0, tyUnderlying)
        Some((List(_ => g1), {
          case NormalizationJudgment(_, _, _, tyUnderlyingN) :: Nil =>
            val tyN = tyUnderlyingN match {
              case SingletonType(_, tN) if Tree.areEqual(v, tN) => tyUnderlyingN
              case _ => SingletonType(tyUnderlyingN, v)
            }
            (true, NormalizationJudgment("NormSingleton", c, ty, tyN))
          case _ =>
            emitErrorWithJudgment("NormSingleton", g, None)
        }))
      }
    case g =>
      None
  })

  val NormExists1 = Rule("NormExists1", {
    case g @ NormalizationGoal(c, ty @ ExistsType(ty1 @ SingletonType(_, _), Bind(id, ty2))) =>
      TypeChecker.debugs(g, "NormExists1")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, ty1)
      val g2: List[Judgment] => Goal = {
        case NormalizationJudgment(_, _, _, tyN1) :: Nil =>
          val c1 = c0.bind(id, tyN1)
          NormalizationGoal(c1, ty2)
        case _ =>
          ErrorGoal(c0, Some(s"Expected normalized type"))
      }
      Some((List(_ => g1, g2), {
        case NormalizationJudgment(_, _, _, _) :: NormalizationJudgment(_, _, _, tyN2) :: Nil =>
          (true, NormalizationJudgment("NormExists1", c, ty, tyN2))
        case _ =>
          emitErrorWithJudgment("NormExists1", g, None)
      }))
    case g =>
      None
  })

  // NOTE: This rule should have lower priority than `NormSubstVar`.
  val NormExists2 = Rule("NormExists2", {
    case g @ NormalizationGoal(c, ty @ ExistsType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "NormExists2")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, ty1)
      val g2: List[Judgment] => Goal = {
        case NormalizationJudgment(_, _, _, tyN1) :: Nil =>
          // TODO: Assert tyN1 is not singleton? (Otherwise we might want to strip the Exists as in NormSubstVar)
          val c1 = c0.bind(id, tyN1)
          NormalizationGoal(c1, ty2)
        case _ =>
          ErrorGoal(c0, Some(s"Expected normalized type"))
      }
      Some((List(_ => g1, g2), {
        case NormalizationJudgment(_, _, _, tyN1) :: NormalizationJudgment(_, _, _, tyN2) :: Nil =>
          (true, NormalizationJudgment("NormExists2", c, ty, ExistsType(tyN1, Bind(id, tyN2))))
        case _ =>
          emitErrorWithJudgment("NormExists2", g, None)
      }))
    case g =>
      None
  })

  val NormNatMatch = Rule("NormNatMatch", {
    case g @ NormalizationGoal(c,
        ty @ NatMatchType(tScrut, tyZero, tySuccBind @ Bind(id, tySucc))) =>
      TypeChecker.debugs(g, "NormNatMatch")
      val c0 = c.incrementLevel
      val tScrutN = Interpreter.evaluateWithContext(interpreterContext(c), tScrut)
      Some(tScrutN match {
        case NatLiteral(n) if n == 0 =>
          val g1 = NormalizationGoal(c0, tyZero)
          (List(_ => g1), {
            case NormalizationJudgment(_, _, _, tyZeroN) :: Nil =>
              (true, NormalizationJudgment("NormNatMatch", c, ty, tyZeroN))
            case _ =>
              emitErrorWithJudgment("NormNatMatch", g, None)
          })
        case NatLiteral(n) =>
          // TODO: Re-type here instead?
          val c1 = c0
            .bind(id, SingletonType(NatType, NatLiteral(n - 1)))
          val g1 = NormalizationGoal(c1, tySucc)
          (List(_ => g1), {
            case NormalizationJudgment(_, _, _, tySuccN) :: Nil =>
              (true, NormalizationJudgment("NormNatMatch", c, ty, tySuccN))
            case _ =>
              emitErrorWithJudgment("NormNatMatch", g, None)
          })
        case _ =>
          (List(), {
            case _ =>
              (true, NormalizationJudgment("NormNatMatch", c, ty, NatMatchType(tScrutN, tyZero, tySuccBind)))
          })
      })
    case g =>
      None
  })

  val NormListMatch = Rule("NormListMatch", {
    case g @ NormalizationGoal(c,
        ty @ ListMatchType(tScrut, tyNil, tyConsBind @ Bind(idHead, Bind(idTail, tyCons)))) =>
      TypeChecker.debugs(g, "NormListMatch")
      val c0 = c.incrementLevel
      val tScrutN = Interpreter.evaluateWithContext(interpreterContext(c), tScrut)
      Some(tScrutN match {
        case LNil() =>
          val g1 = NormalizationGoal(c0, tyNil)
          (List(_ => g1), {
            case NormalizationJudgment(_, _, _, tyNilN) :: Nil =>
              (true, NormalizationJudgment("NormListMatch", c, ty, tyNilN))
            case _ =>
              emitErrorWithJudgment("NormListMatch", g, None)
          })
        case LCons(tHead, tTail) =>
          // TODO: Re-type here instead?
          val c1 = c0
            .bind(idHead, SingletonType(TopType, tHead))
            .bind(idTail, SingletonType(LList, tTail))
          val g1 = NormalizationGoal(c1, tyCons)
          (List(_ => g1), {
            case NormalizationJudgment(_, _, _, tyConsN) :: Nil =>
              (true, NormalizationJudgment("NormListMatch", c, ty, tyConsN))
            case _ =>
              emitErrorWithJudgment("NormListMatch", g, None)
          })
        case _ =>
          (List(), {
            case _ =>
              (true, NormalizationJudgment("NormListMatch", c, ty, ListMatchType(tScrutN, tyNil, tyConsBind)))
          })
      })
    case g =>
      None
  })

  val NormCons = Rule("NormCons", {
    case g @ NormalizationGoal(c, ty @ LConsType(tyHead, tyTail)) =>
      TypeChecker.debugs(g, "NormCons")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, tyHead)
      val g2 = NormalizationGoal(c0, tyTail)
      Some((List(_ => g1, _ => g2), {
        case NormalizationJudgment(_, _, _, tyHeadN) :: NormalizationJudgment(_, _, _, tyTailN) :: Nil =>
          (true, NormalizationJudgment("NormCons", c, ty, LConsType(tyHeadN, tyTailN)))
        case _ =>
          emitErrorWithJudgment("NormCons", g, None)
      }))
    case g =>
      None
  })

  val NormPi = Rule("NormPi", {
    case g @ NormalizationGoal(c, ty @ PiType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "NormPi")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, ty1)
      val g2: List[Judgment] => Goal = {
        case NormalizationJudgment(_, _, _, tyN1) :: Nil =>
          val c1 = c0.bind(id, tyN1)
          NormalizationGoal(c1, ty2)
        case _ =>
          ErrorGoal(c0, None)
      }
      Some((List(_ => g1, g2), {
        case NormalizationJudgment(_, _, _, tyN1) :: NormalizationJudgment(_, _, _, tyN2) :: Nil =>
          (true, NormalizationJudgment("NormPi", c, ty, PiType(tyN1, Bind(id, tyN2))))
        case _ =>
          emitErrorWithJudgment("NormPi", g, None)
      }))
    case g =>
      None
  })

  val NormSigma = Rule("NormSigma", {
    case g @ NormalizationGoal(c, ty @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "NormSigma")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, ty1)
      val g2: List[Judgment] => Goal = {
        case NormalizationJudgment(_, _, _, tyN1) :: Nil =>
          val c1 = c0.bind(id, tyN1)
          NormalizationGoal(c1, ty2)
        case _ =>
          ErrorGoal(c0, None)
      }
      Some((List(_ => g1, g2), {
        case NormalizationJudgment(_, _, _, tyN1) :: NormalizationJudgment(_, _, _, tyN2) :: Nil =>
          (true, NormalizationJudgment("NormSigma", c, ty, SigmaType(tyN1, Bind(id, tyN2))))
        case _ =>
          emitErrorWithJudgment("NormSigma", g, None)
      }))
    case g =>
      None
  })

  val NormBase = Rule("NormBase", {
    case g @ NormalizationGoal(c, TopType | BoolType | NatType | `UnitType` | `LList`) =>
      TypeChecker.debugs(g, "NormBase")
      val c0 = c.incrementLevel
      Some((List(), {
        case _ =>
          (true, NormalizationJudgment("NormBase", c, g.ty, g.ty))
      }))
    case g =>
      None
  })

  def asSingleton(ty: Tree): Tree = {
    var newBindings = List.empty[(Identifier, Tree)]
    def rec(ty: Tree): (Tree, Tree) =
      ty match {
        case SingletonType(tyUnderlying, t) =>
          (tyUnderlying, t)
        case TopType | BoolType | NatType | `UnitType` | `LList` =>
          val id = Identifier.fresh("x")
          newBindings ::= id -> ty
          (ty, Var(id))
        case PiType(ty1, Bind(id, ty2)) =>
          // TODO: To be checked
          val idF = Identifier.fresh("f")
          val tyN = PiType(ty1, Bind(id, asSingleton(ty2)))
          newBindings ::= idF -> tyN
          (tyN, Var(idF))
        case ListMatchType(_, _, _) =>
          // TODO: To be checked
          val idLM = Identifier.fresh("lm")
          newBindings ::= idLM -> ty
          (ty, Var(idLM))
        case NatMatchType(_, _, _) =>
          // TODO: To be checked
          val idNM = Identifier.fresh("nm")
          newBindings ::= idNM -> ty
          (ty, Var(idNM))
        case LConsType(ty1, ty2) =>
          val (ty1UnderlyingN, t1) = rec(ty1)
          val (ty2UnderlyingN, t2) = rec(ty2)
          (LConsType(ty1UnderlyingN, ty2UnderlyingN), LCons(t1, t2))
        case SigmaType(ty1, Bind(id, ty2)) =>
          val (ty1UnderlyingN, t1) = rec(ty1)
          val (ty2UnderlyingN, t2) = rec(ty2)
          (SigmaType(ty1UnderlyingN, Bind(id, ty2UnderlyingN)), Pair(t1, t2))
        case ExistsType(ty1, Bind(id, ty2)) =>
          newBindings ::= id -> ty1
          rec(ty2)
      }
    val (tyUnderlyingN, tN) = rec(ty)
    val tyN = SingletonType(tyUnderlyingN, tN)
    newBindings.foldLeft(tyN) { case (tyAcc, (id, ty)) => ExistsType(ty, Bind(id, tyAcc)) }
  }

  def choosesToExists(ty: Tree): Tree = {
    def replacePaths(tree0: Tree, subst: Map[Tree, Identifier]): Tree = {
      def tryReplace(tree: Tree) =
        subst.get(tree).map(id => Some(Right(Var(id)))).getOrElse(None)
      // This is just to avoid unnecessary hash computations
      tree0.replace {
        case tree @ Var(_) => tryReplace(tree)
        case tree @ LCons(_, _) => tryReplace(tree)
        case tree @ ChooseWithPath(_, _) => tryReplace(tree)
        case _ => None
      }.toOption.get
    }

    def extractPath(tree: Tree, parts: List[BigInt] = List.empty): Option[(List[BigInt], Identifier)] =
      tree match {
        case Var(id) => Some((parts, id))
        case LCons(NatLiteral(i), tTail) => extractPath(tTail, i :: parts)
        case _ => None
      }

    case class Trail(path: List[BigInt], optTy: Option[Tree])

    def trailsOf(rootedIn: Identifier, tree: Tree): Seq[(Tree, Option[Tree])] = {
      var trails = List.empty[Trail]

      // Collect all paths rooted in `rootedIn`
      tree.traversePre { t =>
        val (maybePath, optTy) = t match {
          case ChooseWithPath(ty, path) => (path, Some(ty))
          case App(_, arg) => (arg, None)
          case _ => (UnitLiteral, None) // extractPath will return None
        }
        extractPath(maybePath).foreach {
          case (parts, id) if id == rootedIn => trails = Trail(parts, optTy) :: trails
          case _ =>
        }
      }

      trails = trails.distinct

      // Sort trails lexicographically, ranking "free" occurences lower
      def isSmallerTrail(tr1: Trail, tr2: Trail): Boolean =
        (tr1.path, tr2.path) match {
          case (i1 :: p1, i2 :: p2) =>
            if (i1 < i2) true
            else if (i1 > i2) false
            else isSmallerTrail(Trail(p1, tr1.optTy), Trail(p2, tr2.optTy))
          case (i1 :: p1, Nil) => false
          case (Nil, _ :: _) => true
          case _ => tr1.optTy.isEmpty || tr2.optTy.isDefined
        }

      trails = trails.sortWith(isSmallerTrail)

      // Prune all trails whose paths are prefixed by some other trail's path
      def samePrefix(p1: List[BigInt], p2: List[BigInt]): Boolean =
        p1.zip(p2).forall(ii => ii._1 == ii._2)

      def prunedTrails(trails: Seq[Trail]): Seq[(Tree, Option[Tree])] = {
        var refTrail: Trail = Trail(List(BigInt(-1)), None)
        trails
          .filter {
            case Trail(path, _) if samePrefix(refTrail.path, path) => false
            case trail => refTrail = trail; true
          }
          .map { trail =>
            (trail.path.foldLeft[Tree](Var(rootedIn)) {
              case (acc, i) => LCons(NatLiteral(i), acc)
            }, trail.optTy)
          }
      }

      // Rebuild paths and replacement types.
      trails match {
        case Trail(Nil, None) :: _ => List.empty // No need to replace anything
        case Trail(Nil, optTy) :: _ => List((Var(rootedIn), optTy))
        case trails => prunedTrails(trails)
      }
    }

    def simpleExists(ty: Tree, substs: Map[Tree, Identifier]): Tree = {
      val ExistsType(ty1, Bind(id, ty2)) = ty
      if (id.isFreeIn(ty2))
        ExistsType(recType(ty1, substs), Bind(id, recType(ty2, substs)))
      else
        // TODO: Check that `ty1` is inhabited?
        recType(ty2, substs)
    }

    def recType(ty: Tree, substs: Map[Tree, Identifier]): Tree =
      ty match {
        case SingletonType(tyUnderlying, t) =>
          SingletonType(
            recType(tyUnderlying, substs),
            replacePaths(t, substs))

        case ExistsType(ty1, Bind(id, ty2)) if ty1 == LList && (id.name == "p" || id.name == "q") =>
          // TODO: Implement a rigorous way to identify path existentials ^^^
          val trails = trailsOf(id, ty2)

          if (trails.nonEmpty) {
            val trailsWithIds = trails.map {
              case (tPath, optTy @ None) => (tPath, optTy, Identifier.fresh("q"))
              case (tPath, optTy @ Some(_)) => (tPath, optTy, Identifier.fresh("v"))
            }
            val newSubsts = trailsWithIds.foldLeft(substs) {
              case (substs, (tPath, None, id)) => substs + (tPath -> id)
              case (substs, (tPath, Some(ty), id)) => substs + (ChooseWithPath(ty, tPath) -> id)
            }

            val ty2N = recType(ty2, substs ++ newSubsts)
            assert(!id.isFreeIn(ty2N))

            trailsWithIds.foldRight(ty2N) { case ((_, optTy, id), acc) =>
              ExistsType(optTy.getOrElse(LList), Bind(id, acc))
            }
          } else {
            simpleExists(ty, substs)
          }
        case ExistsType(ty1, Bind(id, ty2)) =>
          simpleExists(ty, substs)

        case TopType | BoolType | NatType | `UnitType` | `LList` =>
          ty
        case PiType(ty1, Bind(id, ty2)) =>
          PiType(recType(ty1, substs), Bind(id, recType(ty2, substs)))
        case ListMatchType(t, tyNil, Bind(id1, Bind(id2, tyCons))) =>
          ListMatchType(replacePaths(t, substs), recType(tyNil, substs),
            Bind(id1, Bind(id2, recType(tyCons, substs))))
        case NatMatchType(t, tyZero, Bind(id, tySucc)) =>
          NatMatchType(replacePaths(t, substs), recType(tyZero, substs),
            Bind(id, recType(tySucc, substs)))
        case LConsType(ty1, ty2) =>
          LConsType(recType(ty1, substs), recType(ty2, substs))
        case SigmaType(ty1, Bind(id, ty2)) =>
          SigmaType(recType(ty1, substs), Bind(id, recType(ty2, substs)))
      }

    recType(ty, Map.empty)
  }

  // NOTE: This only matches on NormalizedSubtypeGoal, which is not a SubtypeGoal,
  //       but yields a SubtypeJudgment!
  val SubNormalize = Rule("SubNormalize", {
    case g @ NormalizedSubtypeGoal(c, ty1, ty2) =>
      TypeChecker.debugs(g, "SubNormalize")
      val c0 = c.incrementLevel
      val g1 = NormalizationGoal(c0, ty1)
      val g2 = NormalizationGoal(c0, ty2)
      val g3: List[Judgment] => Goal = {
        case NormalizationJudgment(_, _, _, tyN1) :: NormalizationJudgment(_, _, _, tyN2) :: Nil =>
          SubtypeGoal(c0, choosesToExists(tyN1), choosesToExists(tyN2))
        case _ =>
          ErrorGoal(c0, Some(s"Expected normalized types"))
      }
      Some((List(_ => g1, _ => g2, g3), {
        case NormalizationJudgment(_, _, _, _) :: NormalizationJudgment(_, _, _, _) ::
          SubtypeJudgment(_, _, _, _) :: Nil => (true, SubtypeJudgment("SubNormalize", c, ty1, ty2))
        case _ =>
          emitErrorWithJudgment("SubNormalize", g, None)
      }))
    case g =>
      None
  })

  // NOTE: Same as SubNormalize; should have higher priority than it
  val SubNormalizeWiden = Rule("SubNormalizeWiden", {
    case g @ NormalizedSubtypeGoal(c, ty1, ty2 @ BaseType()) =>
      TypeChecker.debugs(g, "SubNormalizeWiden")
      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, widen(ty1), ty2)
      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubNormalizeWiden", c, ty1, ty2))
        case _ =>
          emitErrorWithJudgment("SubNormalizeWiden", g, None)
      }))
    case g =>
      None
  })

  def SubReflexive = Rule("SubReflexive", {
    case g @ SubtypeGoal(c, ty1, ty2) if areEqualTrees(ty1, ty2) =>
      TypeChecker.debugs(g, "SubReflexive")
      Some((List(), _ => (true, SubtypeJudgment("SubReflexive", c, ty1, ty2))))
    case g =>
      None
  })

  val SubSingletonReflexive = Rule("SubSingletonReflexive", {
    case g @ SubtypeGoal(c,
        ty1 @ SingletonType(ty1Underlying, t1),
        ty2 @ SingletonType(ty2Underlying, t2)) if areEqualTrees(t1, t2) =>
      TypeChecker.debugs(g, "SubSingletonReflexive")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, ty1Underlying, ty2Underlying)
      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil => (true, SubtypeJudgment("SubSingletonReflexive", c, ty1, ty2))
        case _ => emitErrorWithJudgment("SubSingletonReflexive", g, None)
      }))
    case g =>
      None
  })

  // TODO: See if we can already remove this rule.
  // FIXME: SubtypeGoal on terms t11/t21 and t12/t22 doesn't make sense. Did this work before?
  val SubSingletonCons = Rule("SubSingletonCons", {
    case g @ SubtypeGoal(c,
        ty1 @ SingletonType(ty1Underlying, LCons(t11, t12)),
        ty2 @ SingletonType(ty2Underlying, LCons(t21, t22))) =>
      TypeChecker.debugs(g, "SubSingletonCons")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, ty1Underlying, ty2Underlying)
      val g2 = SubtypeGoal(c0, t11, t21)
      val g3 = SubtypeGoal(c0, t12, t22)
      Some((List(_ => g1, _ => g2, _ => g3), {
        case SubtypeJudgment(_, _, _, _) ::
             SubtypeJudgment(_, _, _, _) ::
             SubtypeJudgment(_, _, _, _) ::
             Nil => (true, SubtypeJudgment("SubSingletonCons", c, ty1, ty2))
        case _ => emitErrorWithJudgment("SubSingletonCons", g, None)
      }))
    case g =>
      None
  })

  // TODO: See if we can already remove this rule.
  // FIXME: Also check underlying types
  val SubSingletonListMatch1 = Rule("SubSingletonListMatch1", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(tyaUnder, ListMatch(taScrut, taNil, Bind(idHeadA, Bind(idTailA, taTail)))),
      tyb @ SingletonType(tybUnder, ListMatch(tbScrut, tbNil, Bind(idHeadB, Bind(idTailB, tbTail))))
    ) if areEqualTrees(taScrut, tbScrut) =>
      TypeChecker.debugs(g, "SubSingletonListMatch1")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0,
        SingletonType(TopType, taNil),
        SingletonType(TopType, tbNil))
      val g2 = SubtypeGoal(c0.bind(idHeadA, TopType).bind(idTailA, LList),
        SingletonType(TopType, taTail),
        SingletonType(TopType, tbTail.replace(idHeadB, Var(idHeadA)).replace(idTailB, Var(idTailA))))
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubSingletonListMatch1", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubSingletonListMatch1", g, None)
      }))

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

  // // NOTE: This version of SubSingletonLeft normalizes `t` to always infer an up-to-date underlying type.
  // //       However, this is not fool-proof -- it might cause type checking to diverge.
  // val SubSingletonLeft = Rule("SubSingletonLeft", {
  //   case g @ SubtypeGoal(c, ty @ SingletonType(_, t), ty2) =>
  //     TypeChecker.debugs(g, "SubSingletonLeft")
  //
  //     val c0 = c.incrementLevel
  //     val v = Interpreter.evaluateWithContext(c0, t)
  //     val g1 = InferGoal(c0, v)
  //     val g2: List[Judgment] => Goal = {
  //       case InferJudgment(_, _, _, SingletonType(ty1N, _)) :: Nil =>
  //         SubtypeGoal(c0, ty1N, ty2)
  //       case _ =>
  //         ErrorGoal(c0, Some("Expected re-typed term to have singleton type"))
  //     }
  //     Some((List(_ => g1, g2), {
  //       case _ :: SubtypeJudgment(_, _, _, _) :: Nil =>
  //         (true, SubtypeJudgment("SubSingletonLeft", c, ty, ty2))
  //       case _ =>
  //         (false, ErrorJudgment("SubSingletonLeft", g, None))
  //     }))
  //   case g =>
  //     None
  // })

  val SubPi = Rule("SubPi", {
    case g @ SubtypeGoal(c,
      tya @ PiType(tya1, Bind(ida, tya2)),
      tyb @ PiType(tyb1, Bind(idb, tyb2))) =>
      TypeChecker.debugs(g, "SubPi")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tyb1, tya1)
      val g2 = NormalizedSubtypeGoal(c0.bind(ida, tyb1), tya2, tyb2.replace(idb, ida))
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubPi", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubPi", g, None)
      }))
    case g =>
      None
  })

  val SubSigma = Rule("SubSigma", {
    case g @ SubtypeGoal(c,
      tya @ SigmaType(tya1, Bind(ida, tya2)),
      tyb @ SigmaType(tyb1, Bind(idb, tyb2))) =>
      TypeChecker.debugs(g, "SubSigma")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tya1, tyb1)
      val g2 = NormalizedSubtypeGoal(c0.bind(ida, tyb1), tya2, tyb2.replace(idb, ida))
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubSigma", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubSigma", g, None)
      }))
    case g =>
      None
  })

  val SubNatMatch = Rule("SubNatMatch", {
    case g @ SubtypeGoal(c,
      tya @ NatMatchType(t, tyZero, Bind(id, tySucc)),
      tyb
    ) =>
      TypeChecker.debugs(g, "SubNatMatch")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tyZero, tyb)
      val g2 = SubtypeGoal(c0.bind(id, NatType), tySucc, tyb)
      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubNatMatch", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubNatMatch", g, None)
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

  val SubSingletonListMatch2 = Rule("SubSingletonListMatch2", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(
        ListMatchType(_, tyNil, Bind(idHead_, Bind(idTail_, tyCons))),
        ListMatch(Var(idScrut), tNil, Bind(idHead, Bind(idTail, tCons)))),
      tyb
    ) if idHead_ == idHead && idTail_ == idTail =>
      TypeChecker.debugs(g, "SubSingletonListMatch2")

      val tyScrut = c.getTypeOf(idScrut).get

      val c1 = c.incrementLevel
        .replaceBinding(idScrut, SingletonType(tyScrut, LNil()))
      val g1 = NormalizedSubtypeGoal(c1, SingletonType(tyNil, tNil), tyb)

      val c2 = c.incrementLevel
        .bind(idHead, TopType)
        .bind(idTail, LList)
        .replaceBinding(idScrut, SingletonType(tyScrut, LCons(Var(idHead), Var(idTail))))
      val g2 = NormalizedSubtypeGoal(c2, SingletonType(tyCons, tCons), tyb)

      Some((List(_ => g1, _ => g2), {
        case SubtypeJudgment(_, _, _, _) :: SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SubSingletonListMatch2", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SubSingletonListMatch2", g, None)
      }))

    case g =>
      None
  })


  val SubExistsLeft = Rule("SubExistsLeft", {
    case g @ SubtypeGoal(c,
      tya @ ExistsType(tya1, Bind(id, tya2)),
      tyb
    ) =>
      TypeChecker.debugs(g, "SubExistsLeft")

      val c0 = c.incrementLevel
      val c1 = c0.bind(id, tya1)
      val g1 = SubtypeGoal(c1, tya2, tyb)
      Some((
        List(_ => g1), {
          case SubtypeJudgment(_, _, _, _) :: Nil =>
            (true, SubtypeJudgment("SubExistsLeft", c, tya, tyb))
          case _ => emitErrorWithJudgment("SubExistsLeft", g, None)
        }
      ))

    case g =>
      None
  })

  val SubExistsRight = Rule("SubExistsRight", {
    case g @ SubtypeGoal(c,
      tya,
      tyb @ ExistsType(ty21, Bind(id2, ty22))
    ) =>
      TypeChecker.debugs(g, "SubExistsRight")

      val optSolution = solve(c, id2, ty21, tya, ty22)
      val c0 = c.incrementLevel

      optSolution match {
        case Some(tSol) if !tSol.freeVars.forall(id => c0.termVariables.contains(id)) =>
          val msg = s"Solver found a candidate solution for $id2, " +
            s"but it's not expressible in the outside context: ${asString(tSol)}"
          rc.reporter.error(msg)
          Some((List(), {
              case _ => emitErrorWithJudgment("SubExistsRight", g, Some(msg))
            }))

        case Some(tSol) =>
          // rc.reporter.info(s"Solver found candidate solution for $id2: ${asString(tSol)}")
          // FIXME: Check that `tSol` is well-formed in `c0`
          val g1 = NormalizedSubtypeGoal(c0, tya, ty22.replace(id2, tSol))
          val g2 = InferGoal(c0, tSol)
          val fg3: List[Judgment] => Goal = {
            case _ :: InferJudgment(_, _, _, ty) :: Nil =>
              SubtypeGoal(c0, ty, ty21)
            case _ =>
              ErrorGoal(c0, None)
          }
          Some((
            List(_ => g1, _ => g2, fg3), {
              case SubtypeJudgment(_, _, _, _) ::
                InferJudgment(_, _, _, _) ::
                SubtypeJudgment(_, _, _, _) :: Nil =>
                  (true, SubtypeJudgment("SubExistsRight", c, tya, tyb))

              case _ => emitErrorWithJudgment("SubExistsRight", g, None)
            }
          ))

        case None =>
          val msg = s"Couldn't find a candidate solution for ${id2.uniqueString}!"
          Some((List(), {
              case _ => emitErrorWithJudgment("SubExistsRight", g, Some(msg))
            }))
      }
    case _ =>
      None
  })

  val InferNatMatch1 = Rule("InferNatMatch1", {
    case g @ InferGoal(c, e @ NatMatch(t, t1, Bind(id, t2))) =>
      TypeChecker.debugs(g, "InferNatMatch1")
      val c0 = c.incrementLevel
      val inferScrutinee = CheckGoal(c0, t, NatType)

      val inferT1 = InferGoal(c0.addEquality(t, NatLiteral(0)), t1)

      val (c1, t2F) = c0.bindAndFreshen(id, NatType, t2)
      val inferT2 = InferGoal(c1.addEquality(t, Succ(Var(id))), t2F)

      Some((
        List(_ => inferScrutinee, _ => inferT1, _ => inferT2), {
          case CheckJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty1) ::
            InferJudgment(_, _, _, ty2) :: _ =>
              val ty = NatMatchType(t, ty1, Bind(id, ty2))
              (true, InferJudgment("InferNatMatch1", c, e,
                SingletonType(ty, e)))

          case _ => emitErrorWithJudgment("InferNatMatch1", g, None)
        }
      ))

    case _ => None
  })

  val InferListMatch = Rule("InferListMatch", {
    case g @ InferGoal(c, e @ ListMatch(t, t1, Bind(idHead, Bind(idTail, t2)))) =>
      TypeChecker.debugs(g, "InferListMatch")
      val c0 = c.incrementLevel
      val inferScrutinee = CheckGoal(c0, t, LList)

      val inferT1 = InferGoal(c0.addEquality(t, LNil()), t1)

      val c1 = c0.bind(idHead, TopType)
      val (c2, t2F) = c1.bindAndFreshen(idTail, LList, t2)
      val inferT2 = InferGoal(c2.addEquality(t, LCons(Var(idHead), Var(idTail))), t2F)

      Some((
        List(_ => inferScrutinee, _ => inferT1, _ => inferT2), {
          case CheckJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty1) ::
            InferJudgment(_, _, _, ty2) :: _ =>
              val ty = ListMatchType(t, ty1, Bind(idHead, Bind(idTail, ty2)))
              (true, InferJudgment("InferListMatch", c, e,
                SingletonType(ty, e)))

          case _ => emitErrorWithJudgment("InferListMatch", g, None)
        }
      ))

    case _ => None
  })

  val SubCons1 = Rule("SubCons1", {
    case g @ SubtypeGoal(c,
      tya @ LConsType(_, _),
      tyb @ `LList`
    ) =>
      TypeChecker.debugs(g, "SubCons1")
      Some((List(), _ => {
        (true, SubtypeJudgment("SubCons1", c, tya, tyb))
      }))

    case _ =>
      None
  })

  val SubCons2 = Rule("SubCons2", {
    case g @ SubtypeGoal(c,
      tya @ LConsType(ty11, ty12),
      tyb @ LConsType(ty21, ty22),
    ) =>
      TypeChecker.debugs(g, "SubCons2")

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, ty11, ty21)
      val g2 = SubtypeGoal(c0, ty12, ty22)
      Some((List(_ => g1, _ => g2), _ => {
        (true, SubtypeJudgment("SubCons2", c, tya, tyb))
      }))

    case _ =>
      None
  })

  object DestructableContext {
    // Only defined when there is something to destruct in `c`
    def unapply(c: Context): Option[Context] = {
      val existsIds = c.termVariables.collect {
        case (id, ExistsType(_, _)) => id
      }
      if (existsIds.nonEmpty) {
        val cNew = c.copy(termVariables = c.termVariables -- existsIds).incrementLevel
        Some(existsIds.foldLeft(cNew) {
          case (acc, id) => acc.bindAndDestruct(id, c.termVariables(id))
        })
      } else {
        None
      }
    }
  }

  val SubDestruct = Rule("SubDestruct", {
    case g @ NormalizedSubtypeGoal(c @ DestructableContext(cNew), tya, tyb) =>
      TypeChecker.debugs(g, "SubDestruct")

      val g1 = NormalizedSubtypeGoal(cNew, tya, tyb)
      Some((List(_ => g1), _ => {
        (true, SubtypeJudgment("SubDestruct", c, tya, tyb))
      }))

    case g @ SubtypeGoal(c @ DestructableContext(cNew), tya, tyb) =>
      TypeChecker.debugs(g, "SubDestruct")

      val g1 = SubtypeGoal(cNew, tya, tyb)
      Some((List(_ => g1), _ => {
        (true, SubtypeJudgment("SubDestruct", c, tya, tyb))
      }))

    case _ =>
      None
  })

  val InferFixWithDefault = Rule("InferFixWithDefault", {
    case g @ InferGoal(c, e @ FixWithDefault(ty, t @ Bind(fIn, tBody), td, tf)) =>
      TypeChecker.debugs(g, "InferFixWithDefault")

      val c0 = c.incrementLevel
      val (c1, tBodyF) = c0.bindAndFreshen(fIn, ty, tBody)
      val g1 = CheckGoal(c1, tBodyF, ty)
      val g2 = CheckGoal(c0, td, ty)
      val g3 = CheckGoal(c0, tf, NatType)

      Some((
        List(_ => g1, _ => g2, _ => g3),
        _ =>
          (true, InferJudgment("InferFixWithDefault", c, e, SingletonType(ty, e)))))

    case _ => None
  })

  val InferFixDep = Rule("InferFixDep", {
    case g @ InferGoal(c, e @ Fix(Some(Bind(idN, ty)), t @ Bind(_, Bind(idT, tBody)))) =>
      TypeChecker.debugs(g, "InferFixDep")

      val c0 = c.incrementLevel
      val (c1, tBodyF) = c0.bindAndFreshen(idT, ty, tBody)
      val g1 = CheckGoal(c1, tBodyF, ty)

      Some((
        List(_ => g1),
        _ =>
          (true, InferJudgment("InferFixDep", c, e, SingletonType(ty, e)))))

    case _ => None
  })

  // === Solver rules ===
  // (Additional rules active in solving mode)
  // FIXME: Check underlying types (irrelevant to soundness, since this is only used for search)

  val SSubListMatchGuessNil = Rule("SSubListMatchGuessNil", {
    case g @ SubtypeGoal(c,
      tya,
      tyb @ SingletonType(_, ListMatch(Var(x), tNil, tCons))
    ) if isUninstTarget(x) =>
      TypeChecker.debugs(g, "SSubListMatchGuessNil")

      instantiateTarget(x, LNil())

      val g1 = NormalizedSubtypeGoal(c.incrementLevel, tya, tyb)

      Some((List(_ => g1), {
        case _ =>
          (true, SubtypeJudgment("SSubListMatchGuessNil", c, tya, tyb))
      }))

    case g =>
      None
  })

  val SSubListMatchGuessCons = Rule("SSubListMatchGuessCons", {
    case g @ SubtypeGoal(c,
      tya,
      tyb @ SingletonType(_, ListMatch(Var(x), tNil, tCons))
    ) if isUninstTarget(x) =>
      TypeChecker.debugs(g, "SSubListMatchGuessCons")

      val idHead = Identifier.fresh("hd")
      val idTail = Identifier.fresh("tl")
      addTarget(idHead, TopType) // FIXME: Should be more precise based on x's type
      addTarget(idTail, LList) // FIXME: Should be more precise based on x's type
      instantiateTarget(x, LCons(Var(idHead), Var(idTail)))

      // FIXME: Why do we run into issues if we remove the new targets on failure?
      def doCleanup() = {
        removeTarget(idHead)
        removeTarget(idTail)
        instantiateTarget(idHead, UnitLiteral)
        instantiateTarget(idTail, LNil())
      }

      val g1 = NormalizedSubtypeGoal(c.incrementLevel, tya, tyb)

      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil =>
          doCleanup()
          (true, SubtypeJudgment("SSubListMatchGuessCons", c, tya, tyb))
        case _ =>
          doCleanup()
          emitErrorWithJudgment("SSubListMatchGuessCons", g, None)
      }))

    case g =>
      None
  })

  object FixWithDefaultMaybeApplied {
    def unapply(t: Tree): Option[Identifier] = t match {
      case App(e1, _) => FixWithDefaultMaybeApplied.unapply(e1)
      case FixWithDefault(_, _, _, Var(xFuel)) => Some(xFuel)
      case _ => None
    }
  }

  val SSubFixWithDefaultGuessZero = Rule("SSubFixWithDefaultGuessZero", {
    case g @ SubtypeGoal(c,
      tya,
      tyb @ SingletonType(_, FixWithDefaultMaybeApplied(xFuel))
    ) if isUninstTarget(xFuel) =>
      TypeChecker.debugs(g, "SSubFixWithDefaultGuessZero")

      instantiateTarget(xFuel, NatLiteral(0))

      val g1 = NormalizedSubtypeGoal(c.incrementLevel, tya, tyb)

      Some((List(_ => g1), {
        case _ =>
          (true, SubtypeJudgment("SSubFixWithDefaultGuessZero", c, tya, tyb))
      }))

    case g =>
      None
  })

  val SSubFixWithDefaultGuessSucc = Rule("SSubFixWithDefaultGuessSucc", {
    case g @ SubtypeGoal(c,
      tya,
      tyb @ SingletonType(_, FixWithDefaultMaybeApplied(xFuel))
    ) if isUninstTarget(xFuel) =>
      TypeChecker.debugs(g, "SSubFixWithDefaultGuessSucc")

      val idFuelPred = Identifier.fresh("f'")
      addTarget(idFuelPred, NatType) // FIXME: Should be more precise based on xFuel's type?
      instantiateTarget(xFuel, Succ(Var(idFuelPred)))

      val g1 = NormalizedSubtypeGoal(c.incrementLevel, tya, tyb)

      Some((List(_ => g1), {
        case _ =>
          (true, SubtypeJudgment("SSubFixWithDefaultGuessSucc", c, tya, tyb))
      }))

    case g =>
      None
  })

/*
  val SSubForcedNilMatch = Rule("SSubForcedNilMatch", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(_, LNil()),
      tyb @ SingletonType(_, ListMatch(Var(x), LNil(), LCons(_, _)))
    ) if isTarget(x) =>
      TypeChecker.debugs(g, "SSubForcedNilMatch")

      instantiateTarget(x, LNil())

      Some((List(), {
        case _ =>
          (true, SubtypeJudgment("SSubForcedNilMatch", c, tya, tyb))
      }))

    case g =>
      None
  })

  val SSubForcedConsMatch = Rule("SSubForcedConsMatch", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(_, LCons(_, _)),
      tyb @ SingletonType(tybUnder, ListMatch(Var(x), LNil(), tb @ LCons(_, _)))
    ) if isTarget(x) =>
      TypeChecker.debugs(g, "SSubForcedConsMatch")

      val xHead = x.freshen()
      val xTail = x.freshen()
      addTarget(xHead, TopType) // FIXME: Should be more precise based on x's type
      addTarget(xTail, LList) // FIXME: Should be more precise based on x's type
      instantiateTarget(x, LCons(Var(xHead), Var(xTail)))

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tya, SingletonType(tybUnder, tb))
      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SSubForcedConsMatch", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SSubForcedConsMatch", g, None)
      }))

    case g =>
      None
  })

  val SSubMatchMatchLeft = Rule("SSubMatchMatchLeft", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(tyaUnder, ListMatch(taScrut, _, _)),
      tyb @ SingletonType(tybUnder, ListMatch(Var(x), _, _))
    ) if isTarget(x) =>
      TypeChecker.debugs(g, "SSubMatchMatchLeft")

      instantiateTarget(x, taScrut)

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tya, tyb)
      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SSubMatchMatchLeft", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SSubMatchMatchLeft", g, None)
      }))

    case g =>
      None
  })

  val SSubMatchMatchRight = Rule("SSubMatchMatchRight", {
    case g @ SubtypeGoal(c,
      tya @ SingletonType(tyaUnder, ListMatch(Var(x), _, _)),
      tyb @ SingletonType(tybUnder, ListMatch(tbScrut, _, _))
    ) if isTarget(x) =>
      TypeChecker.debugs(g, "SSubMatchMatchRight")

      instantiateTarget(x, tbScrut)

      val c0 = c.incrementLevel
      val g1 = SubtypeGoal(c0, tya, tyb)
      Some((List(_ => g1), {
        case SubtypeJudgment(_, _, _, _) :: Nil =>
          (true, SubtypeJudgment("SSubMatchMatchRight", c, tya, tyb))
        case _ =>
          emitErrorWithJudgment("SSubMatchMatchRight", g, None)
      }))

    case g =>
      None
  })
*/
}
