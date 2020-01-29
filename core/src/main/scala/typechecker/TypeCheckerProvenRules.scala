package core
package typechecker

import core.trees._


import Derivation._
import Util._
import Formatting._
import TypeOperators._

object TypeCheckerProvenRules {

  val InferBool = Rule("InferBool", {
    case g @ InferGoal(c, BooleanLiteral(b)) =>
      TypeChecker.debugs(g, "InferBool")
      Some((
        List(),
        _ => (true, InferJudgment("InferBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None
  })

  val CheckBool = Rule("CheckBool", {
    case g @ CheckGoal(c, BooleanLiteral(b), BoolType) =>
      TypeChecker.debugs(g, "CheckBool")
      Some((
        List(),
        _ => (true, CheckJudgment("CheckBool", c, BooleanLiteral(b), BoolType))
      ))
    case g =>
      None
  })

  val InferNat = Rule("InferNat", {
    case g @ InferGoal(c, NatLiteral(n)) =>
      TypeChecker.debugs(g, "InferNat")
      Some((List(), _ => (true, InferJudgment("InferNat", c, NatLiteral(n), NatType))))
    case g =>
      None
  })

  val CheckNat = Rule("CheckNat", {
    case g @ CheckGoal(c, NatLiteral(n), NatType) =>
      TypeChecker.debugs(g, "CheckNat")
      Some((List(), _ => (true, CheckJudgment("CheckNat", c, NatLiteral(n), NatType))))
    case g =>
      None
  })

  val InferUnit = Rule("InferUnit", {
    case g @ InferGoal(c, UnitLiteral) =>
      TypeChecker.debugs(g, "InferUnit")
      Some((List(), _ => (true, InferJudgment("InferUnit", c, UnitLiteral, UnitType))))
    case g =>
      None
  })

  val CheckUnit = Rule("CheckUnit", {
    case g @ CheckGoal(c, UnitLiteral, UnitType) =>
      TypeChecker.debugs(g, "CheckUnit")
      Some((List(), _ => (true, CheckJudgment("CheckUnit", c, UnitLiteral, UnitType))))
    case g =>
      None
  })

  val InferVar = Rule("InferVar", {
    case g @ InferGoal(c, Var(id)) =>
      TypeChecker.debugs(g, "InferVar")
      Some((List(), _ =>
        c.getTypeOf(id) match {
          case None => (false, ErrorJudgment("InferVar", c, id.toString + " is not in context"))
          case Some(tpe) => (true, InferJudgment("InferVar", c, Var(id), tpe))
        }
      ))

    case g =>
      None
  })

  val CheckVar = Rule("CheckVar", {
    case g @ CheckGoal(c, Var(id), ty)
      if c.termVariables.contains(id) && c.termVariables(id).isEqual(ty) =>

      TypeChecker.debugs(g, "CheckVar")
      Some((List(), _ => (true, CheckJudgment("CheckVar", c, Var(id), ty))))
    case g =>
      None
  })

  val InferError = Rule("InferError", {
    case g @ InferGoal(c, e @ Error(_, Some(tp))) =>
      TypeChecker.debugs(g, "InferError")
      val errorGoal = EqualityGoal(c.incrementLevel(), BooleanLiteral(false), BooleanLiteral(true))
      Some((List(_ => errorGoal),
        {
          case AreEqualJudgment(_, _, _, _, _) :: _ => (true, InferJudgment("InferError", c, e, tp))
          case _ => (false, ErrorJudgment("InferError", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val InferLet = Rule("InferLet", {
    case g @ InferGoal(c, e @ LetIn(None, v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case InferJudgment(_, _, _, tyv) :: _ =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            InferGoal(c1, body)
          case _ =>
            ErrorGoal(c, "Could not infer type for " + termOutput(v) + " so we didn't type check the rest.")
        }
      Some((
        List(_ => gv, fgb),
        {
          case _ :: InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, g.toString))
        }
      ))

    case g @ InferGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLet")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gv, _ => gb),
        {
          case CheckJudgment(_, _, _, _) :: InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLet", c, e, tyb))
          case _ =>
            (false, ErrorJudgment("InferLet", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val InferLambda = Rule("InferLambda", {
    case g @ InferGoal(c, e @ Lambda(Some(ty1), Bind(id, body))) =>
      TypeChecker.debugs(g, "InferLambda")
      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferLambda", c, e, PiType(ty1, Bind(id, tyb))))
          case _ =>
            // Returning Top is sound but a bit misleading
            // (true, InferJudgment(c, e, TopType))
            (false, ErrorJudgment("InferLambda", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val InferErasableLambda = Rule("InferErasableLambda", {
    case g @ InferGoal(c, e @ ErasableLambda(ty1, Bind(id, body))) if !id.isFreeIn(body.erase) =>
      TypeChecker.debugs(g, "InferErasableLambda")

      val c1 = c.bind(id, ty1).incrementLevel
      val gb = InferGoal(c1, body)
      Some((
        List(_ => gb),
        {
          case InferJudgment(_, _, _, tyb) :: _ =>
            (true, InferJudgment("InferErasableLambda", c, e, IntersectionType(ty1, Bind(id, tyb))))
          case _ =>
            (false, ErrorJudgment("InferErasableLambda", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val InferIf = Rule("InferIf", {
    case g @ InferGoal(c, e @ IfThenElse(tc, t1, t2)) =>
      TypeChecker.debugs(g, "InferIf")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BooleanLiteral(true))
      val c2 = c0.addEquality(tc, BooleanLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val inferT1 = InferGoal(c1, t1)
      val inferT2 = InferGoal(c2, t2)
      Some((
        List(_ => checkCond, _ => inferT1, _ => inferT2),
        {
          case CheckJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty1) ::
            InferJudgment(_, _, _, ty2) ::
            _ =>
            TypeOperators.ifThenElse(tc, ty1, ty2) match {
              case None => (false,
                ErrorJudgment(
                  "InferIf",
                  c,
                  "Could not infer type for " + termOutput(e) + " with InferIf: cannot unify " +
                  typeOutput(ty1) +  " and  " + typeOutput(ty2)
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
      None
  })

  val InferBinaryPrimitive = Rule("InferBinaryPrimitive", {
    case g @ InferGoal(c, e @ Primitive(op, n1 ::  n2 ::  Nil)) if op.isBinOp =>
      TypeChecker.debugs(g, "InferBinaryPrimitive")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel(), n1, opType)
      val checkN2 = CheckGoal(c.incrementLevel(), n2, opType)
      val checkEq = EqualityGoal(c.incrementLevel(), Primitive(Gteq, List(n1, n2)), BooleanLiteral(true))
      Some((
        if(op == Minus) List(_ => checkN1, _ => checkN2, _ => checkEq) else List(_ => checkN1, _ => checkN2),
        {
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
            (true, InferJudgment("InferBinaryPrimitive", c, e, NatType))
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: _ if op != Minus =>
            (true, InferJudgment("InferBinaryPrimitive", c, e, op.returnedType))
          case _ =>
            (false, ErrorJudgment("InferBinaryPrimitive", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferUnaryPrimitive = Rule("InferUnaryPrimitive", {
    case g @ InferGoal(c, e @ Primitive(op, n1 ::  Nil)) if op.isUnOp =>
      TypeChecker.debugs(g, "InferUnaryPrimitive")
      val opType = op.operandsType
      val checkN1 = CheckGoal(c.incrementLevel(), n1, opType)
      Some((
        List(_ => checkN1),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, InferJudgment("InferUnaryPrimitive", c, e, op.returnedType))
          case _ =>
            (false, ErrorJudgment("InferUnaryPrimitive", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferMatch = Rule("InferMatch", {
    case g @ InferGoal(c, e @ Match(t, t0, Bind(id, tn))) =>
      TypeChecker.debugs(g, "InferMatch")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val inferT0 = InferGoal(c0, t0)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val inferTn = InferGoal(cn, tn)
      Some((
        List(_ => checkN, _ => inferT0, _ => inferTn), {
          case CheckJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty0) ::
            InferJudgment(_, _, _, tyn) :: _ =>

            TypeOperators.matchSimpl(t, ty0, id, tyn) match {
              case None => (false,
                ErrorJudgment(
                  "InferMatch",
                  c,
                  "Cannot unify types " + typeOutput(ty0) + " and " + typeOutput(tyn)
                )
              )
              case Some(ty) => (true, InferJudgment("InferMatch", c, e, ty))
            }

          case _ =>
            (false, ErrorJudgment("InferMatch", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferEitherMatch = Rule("InferEitherMatch", {
    case g @ InferGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2))) =>
      TypeChecker.debugs(g, "InferEitherMatch")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)

      val finferT1: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              InferGoal(c1, t1)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) +  ", found " + typeOutput(ty) + ",  we didn't typecheck the body of either_match")
          }
        case _ => ErrorGoal(c, "Could not infer a type for " + termOutput(t) + " then we didn't typecheck the body of either_match")
      }

      val finferT2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) +  ", found " + typeOutput(ty) + ",  we didn't typecheck the body of either_match")
          }
        case _ => ErrorGoal(c, "Could not infer a type for " + termOutput(t) + " then we didn't typecheck the body of either_match")
      }

      Some((
        List(_ => inferScrutinee, finferT1, finferT2), {
          case InferJudgment(_, _, _, _) ::
            InferJudgment(_, _, _, ty1) ::
            InferJudgment(_, _, _, ty2) :: _ =>
              TypeOperators.eitherMatch(t, id1, ty1, id2, ty2) match {
                case None => (false, ErrorJudgment("InferEitherMatch", c, "Could not unify the types " + typeOutput(ty1) + " " + typeOutput(ty2)))
                case Some(ty) => (true, InferJudgment("InferEitherMatch", c, e, ty))
              }

          case _ => (false, ErrorJudgment("InferEitherMatch", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferFix = Rule("InferFix", {
    case g @ InferGoal(c, e @ Fix(Some(Bind(n, ty)), Bind(n1, Bind(y, t)))) if !n1.isFreeIn(t.erase) =>
      TypeChecker.debugs(g, "InferFix")

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
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, InferJudgment("InferFix", c, e, IntersectionType(NatType, Bind(n, ty))))
          case _ =>
            (false, ErrorJudgment("InferFix", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferForallInstantiation = Rule("InferForallInstantiation", {
    case g @ InferGoal(c, e @ Inst(t1, t2)) =>
      TypeChecker.debugs(g, "InferForallInstantiation")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case IntersectionType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, "Expecting an intersection type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer type for " + termOutput(t1))
      }
      Some((
        List(_ => g1, fg2), {
          case InferJudgment(_, _, _, ty) ::
              CheckJudgment(_, _, _, _) :: _ =>

            dropRefinements(ty) match {
              case IntersectionType(_, Bind(x, ty)) =>
                (true, InferJudgment("InferForallInstantiation", c, e, ty.replace(x, t2)))

              case _ => (false, ErrorJudgment("InferForallInstantiation", c,
                "Could not infer type for " + termOutput(e) + " with InferForallInstantiation: expecting an intersection type for " + 
                termOutput(t1) + ", found " + typeOutput(ty)))
            }

          case _ => (false, ErrorJudgment("InferForallInstantiation", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferApp = Rule("InferApp", {
    case g @ InferGoal(c, e @ App(t1, t2)) =>
      TypeChecker.debugs(g, "InferApp")
      val c0 = c.incrementLevel()
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case PiType(ty2, Bind(_, _)) => CheckGoal(c0, t2, ty2)
            case _ => ErrorGoal(c, "Expecting a Pi type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
          ErrorGoal(c, g1.toString)
      }
      Some((
        List(_ => g1, fg2), {
          case  InferJudgment(_, _, _, ty) ::
                CheckJudgment(_, _, _, _) :: _ =>
            dropRefinements(ty) match {
              case PiType(_, Bind(x, ty)) =>
                (true, InferJudgment("InferApp", c, e, ty.replace(x, t2)))
              case _ => (false, ErrorJudgment("InferApp", c,
                "Could not infer type for " + termOutput(e) + " with InferApp: expecting a Pi type for " +
                termOutput(t1) + ", found: " + typeOutput(ty)))
            }

          case _ =>
            (false, ErrorJudgment("InferApp", c, g.toString))
        }
      ))

    case _ => None
  })

  val UnsafeIgnoreEquality = Rule("In context:\n", {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug("In context:\n" + c.toString)
      TypeChecker.equalityDebug("Ignoring equality: " + g.toString)
      Some(List(), _ => (true, AreEqualJudgment("UnsafeIgnoreEquality", c, t1, t2, bold("IGNORED"))))
    case g =>
      None
  })

  val CheckRefinement = Rule("CheckRefinement", {
    case g @ CheckGoal(c, t, tpe @ RefinementType(ty, Bind(id, b))) =>
      TypeChecker.debugs(g, "CheckRefinement")
      val checkTy = CheckGoal(c.incrementLevel(), t, ty)
      val c1 = c.bind(id, ty).addEquality(Var(id), t)
      val checkRef = EqualityGoal(c1.incrementLevel(), b, BooleanLiteral(true))
      Some((
        List(_ => checkTy, _ => checkRef), {
          case CheckJudgment(_, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
            (true, CheckJudgment("CheckRefinement", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRefinement", c, g.toString))
        }
      ))

    case _ => None
  })

  val CheckReflexive = Rule("CheckReflexive", {
    case g @ CheckGoal(c, t, ty) =>
      TypeChecker.debugs(g, "CheckReflexive")
      val gInfer = InferGoal(c.incrementLevel(), t)
      Some((List(_ => gInfer),
        {
          case InferJudgment(_, _, _, tpe) :: _ if (dropRefinements(tpe) == ty) =>
            (true, CheckJudgment("CheckReflexive", c, t, ty))
          case InferJudgment(_, _, _, tpe) :: _ =>
            (false, ErrorJudgment("CheckReflexive", c,
              "Inferred type " + typeOutput(tpe) + " for " + termOutput(t) +
              ", expected: " + typeOutput(ty)))
          case _ =>
            (false, ErrorJudgment("CheckReflexive", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferPair = Rule("InferPair", {
    case g @ InferGoal(c, e @ Pair(t1, t2)) =>
      TypeChecker.debugs(g, "InferPair")
        val inferFirst = InferGoal(c.incrementLevel(), t1)
        val inferSecond = InferGoal(c.incrementLevel(), t2)
      Some((List(_ => inferFirst, _ => inferSecond),
        {
          case InferJudgment(_, _, _, ty1) :: InferJudgment(_, _, _, ty2) :: _ =>
            val inferredType = SigmaType(ty1, Bind(Identifier(0, "_X"), ty2))
            (true, InferJudgment("InferPair", c, e, inferredType))
          case _ =>
            (false, ErrorJudgment("InferPair", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferFirst = Rule("InferFirst", {
    case g @ InferGoal(c, e @ First(t)) =>
      TypeChecker.debugs(g, "InferFirst")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, SigmaType(ty, _)) :: _ =>
            (true, InferJudgment("InferFirst", c, e, ty))
          case _ =>
            (false, ErrorJudgment("InferFirst", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferSecond = Rule("InferSecond", {
    case g @ InferGoal(c, e @ Second(t)) =>
      TypeChecker.debugs(g, "InferSecond")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, SigmaType(_, Bind(x, ty))) :: _ =>
            (true, InferJudgment("InferSecond", c, e, ty.replace(x, First(t))))
          case _ =>
            (false, ErrorJudgment("InferSecond", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferLeft = Rule("InferLeft", {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.debugs(g, "InferLeft")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, tpe) :: _ =>
            (true, InferJudgment("InferLeft", c, e, SumType(tpe, BottomType)))
          case _ =>
            (false, ErrorJudgment("InferLeft", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferRight = Rule("InferRight", {
    case g @ InferGoal(c, e @ RightTree(t)) =>
      TypeChecker.debugs(g, "InferRight")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, tpe) :: _ =>
            (true, InferJudgment("InferRight", c, e, SumType(BottomType, tpe)))
          case _ =>
            (false, ErrorJudgment("InferRight", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckLeft = Rule("CheckLeft", {
    case g @ CheckGoal(c, e @ LeftTree(t), tpe @ SumType(ty, _)) =>
      TypeChecker.debugs(g, "CheckLeft")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckLeft", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLeft", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckRight = Rule("CheckRight", {
    case g @ CheckGoal(c, e @ RightTree(t), tpe @ SumType(_, ty)) =>
      TypeChecker.debugs(g, "CheckRight")
      val subgoal = CheckGoal(c.incrementLevel(), t, ty)
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckRight", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRight", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckLambda = Rule("CheckLambda", {
    case g @ CheckGoal(c, e @ Lambda(Some(ty1), Bind(id1, body)), tpe @ PiType(ty2, Bind(id2, ty))) if (ty1.isEqual(ty2)) =>
      TypeChecker.debugs(g, "CheckLambda")
      val (freshId, c1) = c.bindFresh(id1.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), body.replace(id1, Var(freshId)), ty.replace(id2, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckLambda", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("CheckLambda", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckPi = Rule("CheckPi", {
    case g @ CheckGoal(c, t, tpe @ PiType(ty1, Bind(id,ty2))) =>
      TypeChecker.debugs(g, "CheckPi")
      val (freshId, c1) = c.bindFresh(id.name, ty1)
      val subgoal = CheckGoal(c1.incrementLevel(), App(t, Var(freshId)), ty2.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckPi", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckPi", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckIf = Rule("CheckIf", {
    case g @ CheckGoal(c, e @ IfThenElse(tc, t1, t2), ty) =>
      TypeChecker.debugs(g, "CheckIf")
      val c0 = c.incrementLevel()
      val c1 = c0.addEquality(tc, BooleanLiteral(true))
      val c2 = c0.addEquality(tc, BooleanLiteral(false))
      val checkCond = CheckGoal(c0, tc, BoolType)
      val checkT1 = CheckGoal(c1, t1, ty)
      val checkT2 = CheckGoal(c2, t2, ty)
      Some((
        List(_ => checkCond, _ => checkT1, _ => checkT2),
        {
          case  CheckJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) ::
                _ =>
            (true, CheckJudgment("CheckIf", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckIf", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val CheckMatch = Rule("CheckMatch", {
    case g @ CheckGoal(c, e @ Match(t, t0, Bind(id, tn)), ty) =>
      TypeChecker.debugs(g, "CheckMatch")
      val c0 = c.incrementLevel()
      val checkN = CheckGoal(c0, t, NatType)
      val checkT0 = CheckGoal(c0, t0, ty)
      val cn = c0.bind(id, NatType).addEquality(Var(id),Primitive(Plus, List(t, NatLiteral(1))))
      val checkTn = CheckGoal(cn, tn, ty)
      Some((
        List(_ => checkN, _ => checkT0, _ => checkTn), {
          case  CheckJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckMatch", c, e, ty))
          case _ => (false, ErrorJudgment("CheckMatch", c, g.toString))
        }
      ))

    case _ => None
  })

  val CheckEitherMatch = Rule("CheckEitherMatch", {
    case g @ CheckGoal(c, e @ EitherMatch(t, Bind(id1, t1), Bind(id2, t2)), tpe) =>
      TypeChecker.debugs(g, "CheckEitherMatch")
      val c0 = c.incrementLevel()
      val inferScrutinee = InferGoal(c0, t)
      val fcheckT1: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c1 = c0.addEquality(t, LeftTree(Var(id1))).bind(id1, ty1)
              CheckGoal(c1, t1, tpe)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) + ", found: " + typeOutput(ty))
          }
        case _ => ErrorGoal(c, "Could not infer a type for: " + termOutput(t))
      }
      val fcheckT2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case SumType(ty1, ty2) =>
              val c2 = c0.addEquality(t, RightTree(Var(id2))).bind(id2, ty2)
              CheckGoal(c2, t2, tpe)
            case _ => ErrorGoal(c, "Expecting a sum type for " + termOutput(t) + ", found: " + typeOutput(ty))
          }
        case _ => ErrorGoal(c, "Could not infer a type for: " + termOutput(t))
      }
      Some((
        List(_ => inferScrutinee, fcheckT1, fcheckT2), {
          case  InferJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) ::
                CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckEitherMatch", c, e, tpe))

          case _ => (false, ErrorJudgment("CheckEitherMatch", c, g.toString))
        }
      ))

    case _ => None
  })

  val CheckPair = Rule("CheckFirst", {
    case g @ CheckGoal(c, e @ Pair(t1, t2), ty @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "CheckFirst")
      val letTy2 = ty2.replace(id, t1)
      val subgoal1 = CheckGoal(c.incrementLevel(), t1, ty1)
      val subgoal2 = CheckGoal(c.incrementLevel(), t2, letTy2)
      Some((List(_ => subgoal1, _ => subgoal2),
        {
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckPair", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckPair", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckSigma = Rule("CheckSigma", {
    case g @ CheckGoal(c, t, tpe @ SigmaType(ty1, Bind(id, ty2))) =>
      TypeChecker.debugs(g, "CheckSigma")
        val checkFirst = CheckGoal(c.incrementLevel(), First(t), ty1)
        val c1 = c.bind(id, ty2).addEquality(Var(id), First(t)).incrementLevel
        val checkSecond = CheckGoal(c1, Second(t), ty2)
      Some((List(_ => checkFirst, _ => checkSecond),
        {
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckSigma", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckSigma", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckIntersection = Rule("CheckIntersection", {
    case g @ CheckGoal(c, t, tpe @ IntersectionType(tyid, Bind(id, ty))) =>
      TypeChecker.debugs(g, "CheckIntersection")
      val (freshId, c1) = c.bindFresh(id.name, tyid)
      val subgoal = CheckGoal(c1.incrementLevel(), Inst(t, Var(freshId)), ty.replace(id, Var(freshId)))
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckIntersection", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckIntersection", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckLet = Rule("CheckLet", {
    case g @ CheckGoal(c, e @ LetIn(None, v, Bind(id, body)), ty) =>
      TypeChecker.debugs(g, "CheckLet")
      val gv = InferGoal(c.incrementLevel(), v)
      val fgb: List[Judgment] => Goal =
        {
          case InferJudgment(_, _, _, tyv) :: _ =>
            val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
            CheckGoal(c1, body, ty)
          case _ =>
            ErrorGoal(c, "Could not infer type for: " + termOutput(v))
        }
      Some((
        List(_ => gv, fgb),
        {
          case _ :: CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, g.toString))
        }
      ))

    case g @ CheckGoal(c, e @ LetIn(Some(tyv), v, Bind(id, body)), ty) =>
      TypeChecker.debugs(g, "CheckLet")
      val gv = CheckGoal(c.incrementLevel(), v, tyv)
      val c1 = c.bind(id, tyv).addEquality(Var(id), v).incrementLevel()
      val gb = CheckGoal(c1, body, ty)
      Some((
        List(_ => gv, _ => gb),
        {
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckLet", c, e, ty))
          case _ =>
            (false, ErrorJudgment("CheckLet", c, g.toString))
        }
      ))

    case g =>
      None
  })

  val InferFold = Rule("InferFold", {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ RecType(n, Bind(a, ty))), t)) =>
      TypeChecker.debugs(g, "InferFold")
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
          case CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: CheckJudgment(_, _, _, _) :: _ =>
            (true, InferJudgment("InferFold", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferFold", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferFoldGen = Rule("InferFoldGen", {
    case g @ InferGoal(c, e @ Fold(Some(tpe @ IntersectionType(NatType, Bind(n, RecType(Var(m), Bind(a, ty))))), t)) if n == m =>
      TypeChecker.debugs(g, "InferFoldGen")
      val nTy = IntersectionType(NatType, Bind(n, RecType(Var(n), Bind(a, ty))))
      val check = CheckGoal(c.incrementLevel(), t, Tree.replace(a, nTy, ty))
      Some((
        List(_ => check),
        {
          case CheckJudgment(_, _, _, _) :: _ if TypeOperators.spos(a, ty) =>
            (true, InferJudgment("InferFoldGen", c, e, tpe))
          case _ =>
            (false, ErrorJudgment("InferFoldGen", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckRecursive = Rule("CheckRecursive", {
    case g @ CheckGoal(c, t, tpe @ RecType(n1, bind1)) =>
      TypeChecker.debugs(g, "CheckRecursive")
      val subgoal = InferGoal(c.incrementLevel(), t)
      val fEquality: List[Judgment] => Goal =
        {
          case InferJudgment(_, _, _, ty2) :: _ =>
            dropRefinements(ty2) match {
              case tpe2 @ RecType(n2, bind2) if (Tree.areEqual(bind1, bind2)) => EqualityGoal(c.incrementLevel(), n1, n2)
              case _ => ErrorGoal(c,
                "Expecting type " + typeOutput(tpe) + " for " + termOutput(t) +
                ", found: " + typeOutput(ty2))
            }
          case _ =>
            ErrorGoal(c, g.toString)
        }
      Some((
        List(_ => subgoal, fEquality),
        {
          case InferJudgment(_, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
            (true, CheckJudgment("CheckRecursive", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckRecursive", c, g.toString))
        }
      ))

    case _ => None
  })

  val CheckTop1 = Rule("CheckTop1", {
    case g @ CheckGoal(c, t, TopType) if t.isValue =>
      TypeChecker.debugs(g, "CheckTop1")
      Some((List(), _ => (true, CheckJudgment("CheckTop1", c, t, TopType))))
    case g =>
      None
  })

  val CheckTop2 = Rule("CheckTop2", {
    case g @ CheckGoal(c, t, TopType) =>
      TypeChecker.debugs(g, "CheckTop2")
      val subgoal = InferGoal(c.incrementLevel(), t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckTop2", c, t, TopType))
          case _ =>
            (false, ErrorJudgment("CheckTop2", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferUnfold = Rule("InferUnfold", {
    case g @ InferGoal(c, e @ Unfold(t1, Bind(x, t2))) =>
      TypeChecker.debugs(g, "InferUnfold")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg2: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
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
            case _ => ErrorGoal(c,
              "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer a type for: " + termOutput(t1))
      }
      val fg3: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
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
            case _ => ErrorGoal(c,
              "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
         ErrorGoal(c, "Could not infer a type for: " + termOutput(t1))
      }
      Some((
        List(_ => g1, fg2, fg3), {
          case  InferJudgment(_, _, _, ty) ::
                InferJudgment(_, _, _, ty1) ::
                j3 ::  _ =>
            dropRefinements(ty) match {
              case IntersectionType(NatType, Bind(n, RecType(m, Bind(a, ty)))) =>
                // FIXME: check strict positive before generating goals
                if (TypeOperators.spos(a, ty)) (true, InferJudgment("InferUnfold", c, e, ty1))
                else (false, ErrorJudgment("InferUnfold", c,
                  "Could not infer type for " + termOutput(e) +
                  " with InferUnFold: " + a.toString + " does not appears strictly positively in " +
                  typeOutput(ty)))

              case RecType(n, Bind(x, ty)) =>
                j3 match {
                  case InferJudgment(_, _, _, ty2) =>
                    if (ty1.isEqual(ty2)) (true, InferJudgment("InferUnfold", c, e, ty1))
                    else {
                      (
                        false,
                        ErrorJudgment(
                          "InferUnfold",
                          c,
                          "Could not infer type for: " + termOutput(e) + " with InferUnfold: " +
                          typeOutput(ty1) + " is not equal to " + typeOutput(ty2)
                        )
                      )
                    }
                  case _ => (false, ErrorJudgment("InferUnfold", c, g.toString))
                }
               case _ =>
                (false, ErrorJudgment("InferUnfold", c,
                  "Expecting a rec type for " + termOutput(t1) + ", found: " + typeOutput(ty)))
            }
          case _ =>
            (false, ErrorJudgment("InferUnfold", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferUnfoldPositive = Rule("InferUnfoldPositive", {
    case g @ InferGoal(c, e @ UnfoldPositive(t1, Bind(x, t2))) =>
      TypeChecker.debugs(g, "InferUnfoldPositive")
      val c0 = c.incrementLevel
      val g1 = InferGoal(c0, t1)
      val fg3: List[Judgment] => Goal = {
        case InferJudgment(_, _, _, ty) :: _ =>
          dropRefinements(ty) match {
            case RecType(n, Bind(a, ty)) =>
              val nTy = Tree.replace(a, RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty)), ty)
              val c2 = c.addEquality(
                t1,
                Fold(Some(RecType(Primitive(Minus, List(n, NatLiteral(1))), Bind(a, ty))), Var(x))
              ).bind(x, nTy)
              InferGoal(c2, t2)
            case _ => ErrorGoal(c,
              "Expecting a rec type for: " + termOutput(t1) + ", found: " + typeOutput(ty))
          }
        case _ =>
          ErrorGoal(c, g1.toString)
      }
      Some((
        List(_ => g1, fg3), {
          case  InferJudgment(_, _, _, _) ::
                InferJudgment(_, _, _, ty2) :: _ =>
            (true, InferJudgment("InferUnfoldPositive", c, e, ty2))
          case _ => (false, ErrorJudgment("InferUnfoldPositive", c, g.toString))
        }
      ))

    case _ => None
  })

  val InferTypeAbs = Rule("InferTypeAbs", {
    case g @ InferGoal(c, e @ Abs(Bind(a, t))) =>
      TypeChecker.debugs(g, "InferTypeAbs")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, tpe) :: _ =>
            (true, InferJudgment("InferTypeAbs", c, e, PolyForallType(Bind(a, tpe))))
          case _ =>
            (false, ErrorJudgment("InferTypeAbs", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val InferTypeApp = Rule("InferTypeApp", {
    case g @ InferGoal(c, e @ TypeApp(t, ty)) =>
      TypeChecker.debugs(g, "InferTypeApp")
      val c1 = c.incrementLevel
      val subgoal = InferGoal(c1, t)
      Some((List(_ => subgoal),
        {
          case InferJudgment(_, _, _, PolyForallType(Bind(x, tpe))) :: _ =>
            (true, InferJudgment("InferTypeApp", c, e, tpe.replace(x, ty)))
          case InferJudgment(_, _, _, ty) :: _ =>
            (false, ErrorJudgment("InferTypeApp", c,
              "Expecting (polymorphic) forall type for: " + termOutput(t) +
              ", found: " + typeOutput(ty)))
          case _ =>
            (false, ErrorJudgment("InferTypeApp", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val CheckTypeAbs = Rule("CheckTypeAbs", {
    case g @ CheckGoal(c, t, tpe @ PolyForallType(Bind(a, ty))) =>
      TypeChecker.debugs(g, "CheckTypeAbs")
      val c1 = c.addTypeVariable(a).incrementLevel
      val subgoal = CheckGoal(c1, TypeApp(t, Var(a)), ty)
      Some((List(_ => subgoal),
        {
          case CheckJudgment(_, _, _, _) :: _ =>
            (true, CheckJudgment("CheckTypeAbs", c, t, tpe))
          case _ =>
            (false, ErrorJudgment("CheckTypeAbs", c,  g.toString))
        }
      ))
    case g =>
      None
  })

  val Reflexivity = Rule("Reflexivity", {
    case g @ EqualityGoal(c, t1, t2) if t1.isEqual(t2) =>
      TypeChecker.debugs(g, "Reflexivity")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment("Reflexivity", c, t1, t2, "By Reflexivity"))
        }
      ))
    case g =>
      None
  })

  def unfoldRefinementInContext(c: Context): Context = {
    c.variables.foldLeft(c) { case (acc, x) =>
      c.getTypeOf(x) match {
        case Some(RefinementType(ty, Bind(y, t2))) =>
          val t2p = t2.replace(y, Var(x))
          c.copy(
            termVariables = c.termVariables.updated(x, ty)
          ).addEquality(t2p, BooleanLiteral(true))
        case _ => acc
      }
    }
  }

  val UnfoldRefinementInContext = Rule("UnfoldRefinementInContext", {
    case g @ EqualityGoal(c, t1, t2) if c.hasRefinementBound =>
      TypeChecker.debugs(g, "UnfoldRefinementInContext")
      val c1 = unfoldRefinementInContext(c)
      val subgoal = EqualityGoal(c1.incrementLevel(), t1, t2)
      Some((List(_ => subgoal),
        {
          case AreEqualJudgment(_, _, _, _, _) :: _ =>
            (true, AreEqualJudgment("UnfoldRefinementInContext", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("UnfoldRefinementInContext", c, g.toString))
        }
      ))
    case g =>
      None
  })

  val EqualityInContext = Rule("EqualityInContext", {
    case g @ EqualityGoal(c, t1, t2) if
      c.variables.exists(v =>
        c.termVariables.contains(v) && (
          c.termVariables(v) == EqualityType(t1,t2) ||
          c.termVariables(v) == EqualityType(t2,t1)
        )
      )
      =>
      TypeChecker.debugs(g, "EqualityInContext")
      Some((List(),
        {
          case _ => (true, AreEqualJudgment("EqualityInContext", c, t1, t2, "By Assumption"))
        }
      ))
    case g =>
      None
  })
}
