package core
package typechecker

import core.trees._

import util.RunContext
import util.Utils._

import Derivation._
import TypeOperators._

trait TypeCheckerUnprovenRules {

  val rc: RunContext

  val InferLeft = Rule("InferLeft", {
    case g @ InferGoal(c, e @ LeftTree(t)) =>
      TypeChecker.debugs(rc, g, "InferLeft")
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
      TypeChecker.debugs(rc, g, "InferRight")
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

  val NatEqualToEqual = Rule("NatEqualToEqual", {
    case g @ EqualityGoal(c, Primitive(Eq, t1 ::  t2 ::  Nil), BooleanLiteral(true)) =>
      TypeChecker.debugs(rc, g, "NatEqualToEqual")

      Some((List(
        _ => EqualityGoal(c.incrementLevel(), t1, t2),
        _ => CheckGoal(c.incrementLevel(), t1, NatType),
        _ => CheckGoal(c.incrementLevel(), t2, NatType)
        ),
        {
          case
            AreEqualJudgment(_, _, _, _, _) ::
            CheckJudgment(_, _, _, _) ::
            CheckJudgment(_, _, _, _) :: _ =>
            (true, AreEqualJudgment("NatEqualToEqual", c, Primitive(Eq, t1 ::  t2 ::  Nil), BooleanLiteral(true), ""))
          case _ =>
            (false, ErrorJudgment("NatEqualToEqual", c, g.toString))
        }
      ))
    case g =>
      None
  })

  def findEquality(l: List[Identifier], termVariables: Map[Identifier, Tree], id: Identifier): Option[Tree] = l match {
    case Nil => None
    case v ::  vs if termVariables.contains(v) => termVariables(v) match {
      case EqualityType(Var(id2), t) if id == id2 =>
        Some(t)
      case EqualityType(t, Var(id2)) if id == id2 && !t.isInstanceOf[Var] =>
        Some(t)
      case _ => findEquality(vs, termVariables, id)
    }
    case v ::  vs => findEquality(vs, termVariables, id)
  }

  // This function expands variables in a tree, but shouldn't go under lambdas
  // For a term t, it should hold that if expandVars(c, t) = Some(t'), then c ⊢ t ≡ t'
  // For a type ty, it should hold that if expandVars(c, ty) = Some(ty'), then
  // for all substitutions consistent with c, the denotations of ty and ty'
  // are the same.
  def expandVars(c: Context, t: Tree): Option[Tree] = t match {
    case Var(id) => findEquality(c.variables, c.termVariables, id)
    case Primitive(op, args) =>
      mapFirst2(args, (arg: Tree) => expandVars(c, arg)).map(newArgs =>
        Primitive(op, newArgs)
      )
    case App(t1, t2) =>
      expandVars(c, t1).map[Tree](newT1 => App(newT1, t2)) orElse
      expandVars(c, t2).map[Tree](newT2 => App(t1, newT2))
    case EqualityType(t1, t2) =>
      expandVars(c, t1).map[Tree](newT1 => EqualityType(newT1, t2)) orElse
      expandVars(c, t2).map[Tree](newT2 => EqualityType(t1, newT2))
    case _ => None
  }

  def expandVars(c: Context, l: List[Identifier]): Option[Context] = l match {
    case Nil => None
    case v ::  vs if c.termVariables.contains(v) =>
      expandVars(c.copy(variables = l.tail), c.termVariables(v)).map(
        ty => c.copy(termVariables = c.termVariables.updated(v, ty))
      ) orElse expandVars(c, vs)
    case _ ::  vs => expandVars(c, vs)
  }

  def expandVars(c: Context): Option[Context] = expandVars(c, c.variables)

  def expandVars(g: Goal): Option[Goal] = g match {
    case InferGoal(c, t) =>
      expandVars(c).map(newC => InferGoal(newC, t): Goal) orElse
      expandVars(c, t).map(newT => InferGoal(c, newT): Goal)
    case CheckGoal(c, t, tp) =>
      expandVars(c).map(newC => CheckGoal(newC, t, tp): Goal) orElse
      expandVars(c, t).map(newT => CheckGoal(c, newT, tp): Goal) orElse
      expandVars(c, tp).map(newTp => CheckGoal(c, t, newTp): Goal)
    case EqualityGoal(c, t1, t2) =>
      expandVars(c).map(newC => EqualityGoal(newC, t1, t2): Goal) orElse
      expandVars(c, t1).map(newT1 => EqualityGoal(c, newT1, t2): Goal) orElse
      expandVars(c, t2).map(newT2 => EqualityGoal(c, t1, newT2): Goal)
    case SynthesisGoal(c, tp) =>
      expandVars(c).map(newC => SynthesisGoal(newC, tp): Goal) orElse
      expandVars(c, tp).map(newTp => SynthesisGoal(c, newTp): Goal)
    case _ => None
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], g: Goal): Option[(Goal, T)] = g match {
    case InferGoal(c, t) =>
      lift(f, c, t).map { case (newT, a) => (InferGoal(c, newT): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case CheckGoal(c, t, tp) =>
      lift(f, c, t).map { case (newT, a) => (CheckGoal(c, newT, tp): Goal, a) } orElse
      lift(f, c, tp).map { case (newTp, a) => (CheckGoal(c, t, newTp): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case EqualityGoal(c, t1, t2) =>
      lift(f, c, t1).map { case (newT1, a) => (EqualityGoal(c, newT1, t2): Goal, a) } orElse
      lift(f, c, t2).map { case (newT2, a) => (EqualityGoal(c, t1, newT2): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case SynthesisGoal(c, tp) =>
      lift(f, c, tp).map { case (newTp, a) => (SynthesisGoal(c, newTp): Goal, a) } orElse
      lift(f, c).map { case (newContext, a) => (g.updateContext(newContext), a) }
    case _ => None
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context, l: List[Identifier]): Option[(Context, T)] = {
    l match {
      case Nil => None
      case v ::  vs if c.termVariables.contains(v) =>
        lift(f, c.copy(variables = vs), c.termVariables(v)).map {
          case (e, a) =>
            (c.copy(termVariables = c.termVariables.updated(v, e)), a)
        } orElse {
          lift(f, c, vs)
        }
      case v ::  vs => lift(f, c, vs)
    }
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context): Option[(Context, T)] = {
    lift(f, c, c.variables)
  }

  def lift[T](f: (Context, Tree) => Option[(Tree, T)], c: Context, t: Tree): Option[(Tree, T)] = f(c, t) orElse {
    t match {
      case EqualityType(t1, t2) =>
        lift(f, c, t1).map { case (newT1, x) => (EqualityType(newT1, t2): Tree, x) } orElse
        lift(f, c, t2).map { case (newT2, x) => (EqualityType(t1, newT2): Tree, x) }
      case Primitive(op, args) =>
        mapFirstWithResult(args, (arg: Tree) => lift(f, c, arg)).map {
          case (newArgs, x) => (Primitive(op, newArgs), x)
        }
      case _ => None
    }
  }

  val ExpandVars = Rule("ExpandVars", {
    case g @ EqualityGoal(c, t1, t2) =>
      expandVars(g).map { sg =>
        TypeChecker.debugs(rc, g, "ExpandVars")
        (List(_ => sg), {
          case AreEqualJudgment(_, _, _, _, _) :: _ =>
            (true, AreEqualJudgment("ExpandVars", c, t1, t2, ""))
          case _ =>
            (false, ErrorJudgment("ExpandVars", c, g.toString))
        })
      }
    case g =>
      None
  })

  def inlineApplicationsTop(c: Context, e: Tree): Option[(Tree, (Goal, Identifier))] = {
    e match {
      case App(Lambda(tp, Bind(id, body)), t) =>
        val subgoal = if (tp.isEmpty) InferGoal(c, t) else CheckGoal(c, t, tp.get)
        val (freshId, _) = c.getFresh(id.name)
        Some(body.replace(id, Var(freshId)), (subgoal, freshId))

      case LetIn(tp, value, body) => inlineApplicationsTop(c, App(Lambda(tp, body), value))

      case _ => None
    }
  }

  val InlineApplications = Rule("InlineApplications", {
    case g @ EqualityGoal(c, t1, t2) =>

      val res = lift((c: Context, t: Tree) => inlineApplicationsTop(c, t), g)

      res.map {
        case (g2, (subgoal, freshId)) =>
          def newGoal(prev: List[Judgment]): Goal = prev match {
            case InferJudgment(_, _, t, tp) :: Nil =>
              val c1 = g2.c.incrementLevel().bind(freshId, tp)
              val c2 = c1.addEquality(Var(freshId), t)
              g2.updateContext(c2)
            case CheckJudgment(_, _, t, tp) :: Nil =>
              val c1 = g2.c.incrementLevel().bind(freshId, tp)
              val c2 = c1.addEquality(Var(freshId), t)
              g2.updateContext(c2)
            case _ => ErrorGoal(c, "Attempted to inline an application or a val, but could not type check the argument.")
          }
          (List(_ => subgoal, newGoal), {
            case _ :: AreEqualJudgment(_, _, _, _, _) :: _ =>
              (true, AreEqualJudgment("InlineApplications", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("InlineApplications", c, g.toString))
          })
      }

    case g =>
      None
  })

  def topIf(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case IfThenElse(tc, tt, tf) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, BooleanLiteral(true))
        val c2 = c0.addEquality(tc, BooleanLiteral(false))
        val checkC = CheckGoal(c0, tc, BoolType)
        val equalT1 = EqualityGoal(c1, tt, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => checkC, _ => equalT1, _ => equalT2),
          {
            case CheckJudgment(_, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
              (true, AreEqualJudgment("TopIf", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("TopIf", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None
    }
  }

  val TopIf = Rule("TopIf", {
    case g @ EqualityGoal(c, t1 @ IfThenElse(tc, tt, tf), t2) =>
      TypeChecker.debugs(rc, g, "TopIf")
      topIf(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ IfThenElse(tc, tt, tf)) =>
      TypeChecker.debugs(rc, g, "TopIf")
      topIf(c, t2, t1)
    case g =>
      None
  })


  def topMatch(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case Match(tc, t0, Bind(y, tf)) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, NatLiteral(0))
        val c2 = c0.addEquality(tc, Primitive(Plus, List(Var(y), NatLiteral(1)))).bind(y, NatType)
        val checkC = CheckGoal(c0, tc, NatType)
        val equalT1 = EqualityGoal(c1, t0, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => checkC, _ => equalT1, _ => equalT2),
          {
            case CheckJudgment(_, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
              (true, AreEqualJudgment("TopMatch", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("TopMatch", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None
    }
  }

  val TopMatch = Rule("TopMath", {
    case g @ EqualityGoal(c, t1 @ Match(tc, tt, tf), t2) =>
      TypeChecker.debugs(rc, g, "TopMath")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ Match(tc, tt, tf)) =>
      TypeChecker.debugs(rc, g, "TopMatch")
      topEitherMatch(c, t2, t1)
    case g =>
      None
  })


  // FIXME: infer the type of `tc`
  def topEitherMatch(c: Context, t1: Tree, t2: Tree): Option[(List[List[Judgment] => Goal], List[Judgment] => (Boolean, Judgment))] = {
    t1 match {
      case EitherMatch(tc, Bind(x, tt), Bind(y, tf)) =>
        val c0 = c.incrementLevel()
        val c1 = c0.addEquality(tc, LeftTree(Var(x)))
        val c2 = c0.addEquality(tc, RightTree(Var(y)))
        val equalT1 = EqualityGoal(c1, tt, t2)
        val equalT2 = EqualityGoal(c2, tf, t2)
        Some((
          List(_ => equalT1, _ => equalT2),
          {
            case AreEqualJudgment(_, _, _, _, _) :: AreEqualJudgment(_, _, _, _, _) :: _ =>
              (true, AreEqualJudgment("TopEitherMatch", c, t1, t2, ""))
            case _ =>
              (false, ErrorJudgment("TopEitherMatch", c, EqualityGoal(c, t1, t2).toString))
          }
        ))
      case _ => None
    }
  }

  val TopEitherMatch = Rule("TopEitherMath", {
    case g @ EqualityGoal(c, t1 @ EitherMatch(tc, tt, tf), t2) =>
      TypeChecker.debugs(rc, g, "TopEitherMath")
      topEitherMatch(c, t1, t2)
    case g @ EqualityGoal(c, t1, t2 @ EitherMatch(tc, tt, tf)) =>
      TypeChecker.debugs(rc, g, "TopEitherMatch")
      topEitherMatch(c, t2, t1)
    case g =>
      None
  })
}
