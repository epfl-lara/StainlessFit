/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package trees

import util.RunContext
import parser.FitParser

case class Var(id: Identifier) extends Tree {
  setPos(id)
}

case class NatLiteral(n: BigInt) extends Tree {
  require(n >= 0)
}

case class Succ(t: Tree) extends Tree
case object UnitLiteral extends Tree
case class BooleanLiteral(b: Boolean) extends Tree
case class Bind(id: Identifier, body: Tree) extends Tree
case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree
case class Lambda(tp: Option[Tree], bind: Tree) extends Tree
case class ErasableLambda(ty: Tree, bind: Tree) extends Tree
case class App(t1: Tree, t2: Tree) extends Tree
case class Pair(t1: Tree, t2: Tree) extends Tree
case class Size(t: Tree) extends Tree
case class First(t: Tree) extends Tree
case class Second(t: Tree) extends Tree
case class Fix(tp: Option[Tree], bind: Tree) extends Tree
case class NatMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class LeftTree(t: Tree) extends Tree
case class RightTree(t: Tree) extends Tree
case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree
case class MacroTypeDecl(tp: Tree, body: Tree) extends Tree
case class MacroTypeInst(v: Tree, args: List[(Boolean, Tree)]) extends Tree
case class Error(s: String, t: Option[Tree]) extends Tree
case class Primitive(op: Operator, args: List[Tree]) extends Tree
case class ErasableApp(t1: Tree, t2: Tree) extends Tree
case class Refl(t1: Tree, t2: Tree) extends Tree
case class Fold(tp: Tree, t: Tree) extends Tree
case class Unfold(t: Tree, bind: Tree) extends Tree
case class UnfoldPositive(t: Tree, bind: Tree) extends Tree
case class Abs(t: Tree) extends Tree
case class TypeApp(t1: Tree, t2: Tree) extends Tree
case object BottomType extends Tree
case object TopType extends Tree
case object UnitType extends Tree
case object BoolType extends Tree
case object NatType extends Tree
case class SigmaType(t1: Tree, t2: Tree) extends Tree
case class SumType(t1: Tree, t2: Tree) extends Tree
case class PiType(t1: Tree, t2: Tree) extends Tree
case class IntersectionType(t1: Tree, t2: Tree) extends Tree
case class ExistsType(t1: Tree, t2: Tree) extends Tree
case class RefinementType(t1: Tree, t2: Tree) extends Tree
case class RefinementByType(t1: Tree, t2: Tree) extends Tree
case class RecType(n: Tree, bind: Tree) extends Tree
case class PolyForallType(t: Tree) extends Tree
case class UnionType(t1: Tree, t2: Tree) extends Tree
case class EqualityType(t1: Tree, t2: Tree) extends Tree
case class Because(t1: Tree, t2: Tree) extends Tree
case class Node(name: String, children: List[Tree]) extends Tree

object Tree {

  def deconstruct(t: Tree): (List[Tree], List[Tree] => Tree) = {
    t match {
      case Var(_) => (Nil, _ => t)
      case UnitLiteral => (Nil, _ => t)
      case NatLiteral(_) => (Nil, _ => t)
      case BooleanLiteral(_) => (Nil, _ => t)
      case IfThenElse(cond, t1, t2) => (
        List(cond, t1, t2), {
          case newCond :: newT1 :: newT2 :: Nil => IfThenElse(newCond, newT1, newT2)
        }
      )
      case App(t1, t2) => (List(t1, t2), { case newT1 :: newT2 :: Nil => App(newT1, newT2) })
      case Pair(t1, t2) => (List(t1, t2), { case newT1 :: newT2 :: Nil => Pair(newT1, newT2) })
      case Size(t) => (List(t), { case newT :: Nil => Size(newT) })
      case First(t) => (List(t), { case newT :: Nil => First(newT) })
      case Second(t) => (List(t), { case newT :: Nil => Second(newT) })
      case LeftTree(t) => (List(t), { case newT :: Nil => LeftTree(newT) })
      case RightTree(t) => (List(t), { case newT :: Nil => RightTree(newT) })
      case Because(t1, t2) => (List(t1, t2), { case newT1 :: newT2 :: Nil => Because(newT1, newT2) })
      case Bind(id, t) => (List(t), { case newT :: Nil => Bind(id, newT) })
      case Lambda(None, bind) => (List(bind), { case newBind :: Nil => Lambda(None, newBind) })
      case Lambda(Some(tp), bind) => (List(tp, bind), { case newTp :: newBind :: Nil => Lambda(Some(newTp), newBind) })
      case ErasableLambda(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => ErasableLambda(newTp, newBind) })
      case Fix(None, bind) => (List(bind), { case newBind :: Nil => Fix(None, newBind) })
      case Fix(Some(tp), bind) => (List(tp, bind), { case newTp :: newBind :: Nil => Fix(Some(newTp), newBind) })
      case LetIn(None, v1, bind) => (List(v1, bind), { case newV1 :: newBind :: Nil => LetIn(None, newV1, newBind) })
      case LetIn(Some(tp), v1, bind) => (List(tp, v1, bind),
        { case newTp :: newV1 :: newBind :: Nil => LetIn(Some(newTp), newV1, newBind)
      })
      case MacroTypeDecl(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => MacroTypeDecl(newTp, newBind) })
      case MacroTypeInst(t, args) =>
        (t :: args.map(_._2), { case newT :: newArgs => MacroTypeInst(newT, args.map(_._1).zip(newArgs)) })
      case NatMatch(t, t0, bind) =>
        (List(t, t0, bind), { case newT :: newT0 :: newBind :: Nil => NatMatch(newT, newT0, newBind) })
      case EitherMatch(t, bind1, bind2) =>
        (List(t, bind1, bind2), { case newT :: newBind1 :: newBind2 :: Nil => EitherMatch(newT, newBind1, newBind2) })
      case Primitive(op, args) => (args, newArgs => Primitive(op, newArgs))
      case ErasableApp(t1, t2) => (List(t1, t2), { case newT1 :: newT2 :: Nil => ErasableApp(newT1, newT2) })
      case Fold(tp, t) => (List(tp, t), { case newTp :: newT :: Nil => Fold(newTp, newT) })
      case Unfold(t, bind) => (List(t, bind), { case newT :: newBind :: Nil => Unfold(newT, newBind) })
      case UnfoldPositive(t, bind) => (List(t, bind), { case newT :: newBind :: Nil => UnfoldPositive(newT, newBind) })
      case Abs(bind) => (List(bind), { case newBind :: Nil => Abs(newBind) })
      case TypeApp(t, tp) =>  (List(t, tp), { case newT :: newTp :: Nil => TypeApp(newT, newTp) })
      case Error(s, None) => (Nil, _ => t)
      case Error(s, Some(tp)) => (List(tp), { case newTp :: Nil => Error(s, Some(newTp)) })

      case NatType => (Nil, _ => t)
      case BoolType => (Nil, _ => t)
      case UnitType => (Nil, _ => t)
      case SumType(tp1, tp2) => (List(tp1, tp2), { case newTp1 :: newTp2 :: Nil => SumType(newTp1, newTp2) })
      case PiType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => PiType(newTp, newBind) })
      case SigmaType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => SigmaType(newTp, newBind) })
      case IntersectionType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => IntersectionType(newTp, newBind) })
      case ExistsType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => ExistsType(newTp, newBind) })
      case RefinementType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => RefinementType(newTp, newBind) })
      case RefinementByType(tp, bind) => (List(tp, bind), { case newTp :: newBind :: Nil => RefinementByType(newTp, newBind) })
      case EqualityType(t1, t2) => (List(t1, t2), { case newT1 :: newT2 :: Nil => EqualityType(newT1, newT2) })
      case RecType(t, bind) => (List(t, bind), { case newT :: newBind :: Nil => RecType(newT, newBind) })
      case PolyForallType(bind) => (List(bind), { case newBind :: Nil => PolyForallType(newBind) })
      case Node(name, children) => (children, newChildren => Node(name, newChildren))

      case BottomType => (Nil, _ => t)
      case TopType => (Nil, _ => t)
    }
  }

  def isValue(e: Tree): Boolean = {
    e match {
      case UnitLiteral => true
      case NatLiteral(_) => true
      case BooleanLiteral(_) => true
      case Lambda(_, _) => true
      case Pair(t1, t2) => isValue(t1) && isValue(t2)
      case RightTree(t) => isValue(t)
      case LeftTree(t) => isValue(t)
      case _ => false
    }
  }

  trait Solver {
    def targets: Map[Identifier, Option[Tree]]
    def recordSolution(x: Identifier, t: Tree): Unit
    def addTarget(x: Identifier): Unit
  }

  object Solver {
    implicit val defaultSolver: Solver = null
    def targets(x: Identifier)(implicit solver: Solver) =
      if (solver ne null) solver.targets.contains(x) else false
  }

  def areEqual(t1: Tree, t2: Tree)(implicit rc: RunContext, solver: Solver): Boolean = {
    (t1, t2) match {
      case (IfThenElse(cond1, t11, t12), IfThenElse(cond2, t21, t22)) =>
        areEqual(cond1, cond2) && areEqual(t11, t21) && areEqual(t12, t22)
      case (App(t11, t12), App(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Pair(t11, t12), Pair(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (First(t1), First(t2)) => areEqual(t1, t2)
      case (Second(t1), Second(t2)) => areEqual(t1, t2)
      case (LeftTree(t1), LeftTree(t2)) => areEqual(t1, t2)
      case (RightTree(t1), RightTree(t2)) => areEqual(t1, t2)
      case (Because(t11, t12), Because(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Bind(x1, t1), Bind(x2, t2)) => areEqual(t1, t2.replace(x2, Var(x1)))
      case (Lambda(None, bind1), Lambda(None, bind2)) => areEqual(bind1, bind2)
      case (Lambda(Some(tp1), bind1), Lambda(Some(tp2), bind2)) => areEqual(tp1, tp2) && areEqual(bind1, bind2)
      case (ErasableLambda(tp1, bind1), ErasableLambda(tp2, bind2)) => areEqual(tp1, tp2) && areEqual(bind1, bind2)
      case (Fix(_, bind1), Fix(_, bind2)) => areEqual(bind1, bind2)
      case (LetIn(_, v1, bind1), LetIn(_, v2, bind2)) => areEqual(v1, v2) && areEqual(bind1, bind2)
      case (MacroTypeDecl(tpe1, bind1), MacroTypeDecl(tpe2, bind2)) => areEqual(tpe1, tpe2) && areEqual(bind1, bind2)
      case (MacroTypeInst(v1, args1), MacroTypeInst(v2, args2)) =>
        if (areEqual(v1, v2) && args1.size == args2.size)
          args1.zip(args2).forall { case (p1, p2) =>
            p1._1 == p2._1 &&
            areEqual(p1._2, p2._2)
          }
        else
          false
      case (NatMatch(n1, t1, bind1), NatMatch(n2, t2, bind2)) => areEqual(n1, n2) && areEqual(t1, t2) && areEqual(bind1, bind2)
      case (EitherMatch(t1, bind11, bind12), EitherMatch(t2, bind21, bind22)) =>
        areEqual(t1, t2) && areEqual(bind11, bind21) && areEqual(bind12, bind22)
      case (Primitive(op1, args1), Primitive(op2, args2)) =>
        if (op1 == op2 && args1.size == args2.size) args1.zip(args2).forall { case (t1, t2) => areEqual(t1, t2)}
        else false
      case (ErasableApp(t11, t12), ErasableApp(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Fold(tp1, t1), Fold(tp2, t2)) => areEqual(tp1, tp2) && areEqual(t1, t2)
      case (Unfold(t1, bind1), Unfold(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (UnfoldPositive(t1, bind1), UnfoldPositive(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (Abs(bind1), Abs(bind2)) => areEqual(bind1, bind2)
      case (TypeApp(abs1, t1), TypeApp(abs2, t2)) => areEqual(abs1, abs2) && areEqual(t1, t2)
      case (SumType(t1, bind1), SumType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PiType(t1, bind1), PiType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (SigmaType(t1, bind1), SigmaType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (IntersectionType(t1, bind1), IntersectionType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (ExistsType(t1, bind1), ExistsType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RefinementType(t1, bind1), RefinementType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RefinementByType(t1, bind1), RefinementByType(t2, bind2)) =>
        if (solver eq null)
          areEqual(t1, t2) && areEqual(bind1, bind2)
        else
          areEqual(bind1, bind2)
      case (EqualityType(t11, t12), EqualityType(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (RecType(t1, bind1), RecType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => areEqual(bind1, bind2)
      case (Node(name1, args1), Node(name2, args2)) => name1 == name2 && args1.zip(args2).forall { case (arg1, arg2) => areEqual(arg1, arg2) }
      case (Var(x), _) if Solver.targets(x) => solver.recordSolution(x, t2); true
      case (_, Var(x)) if Solver.targets(x) => solver.recordSolution(x, t1); true
      case _ => t1 == t2
    }
  }
}

sealed abstract class Tree extends Positioned {
  def traverse(pre: Tree => Unit, post: Tree => Unit): Unit = {
    pre(this)
    val (children, reconstruct) = this.deconstruct
    for (child <- children) child.traverse(pre, post)
    post(this)
  }

  def traversePost(f: Tree => Unit): Unit = traverse(_ => (), f)
  def traversePre(f: Tree => Unit): Unit = traverse(f, _ => ())

  def mapChildren(f: Tree => Tree): Tree = {
    val (children, reconstruct) = this.deconstruct
    reconstruct(children.map(f))
  }

  def postMap(p: Tree => Tree => Tree): Tree = {
    val resultTransformer = p(this)
    resultTransformer(this.mapChildren(_.postMap(p)))
  }

  def preMap(p: Tree => Option[Tree]): Tree = {
    p(this) match {
      case Some(e) => e.preMap(p)
      case None => this.mapChildren(_.preMap(p))
    }
  }

  def exists(guard: Tree => Boolean, p: Tree => Boolean): Boolean = {
    guard(this) && (p(this) || this.deconstruct._1.exists(_.exists(guard, p)))
  }

  def asString(implicit rc: RunContext): String = Printer.asString(this)

  def isValue: Boolean = Tree.isValue(this)

  def isEqual(t: Tree)(implicit rc: RunContext): Boolean = Tree.areEqual(this, t)

  def deconstruct = Tree.deconstruct(this)

  def replace(p: Tree => Option[Either[String,Tree]], post: Tree => Unit): Either[String,Tree] = {
    val res = p(this).getOrElse {
      val (children, reconstruct) = this.deconstruct
      children.foldRight(Right(Nil): Either[String, List[Tree]]) { (child, acc) =>
        acc.flatMap(newChildren => child.replace(p, post).map(newChild => newChild :: newChildren))
      }.map(reconstruct)
    }
    for (t <- res) post(t)
    res
  }
  def replace(p: Tree => Option[Either[String,Tree]]): Either[String,Tree] = replace(p, _ => ())

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Tree = replace((e: Tree) => e match {
    case Var(id2) if id2 == id => Some(Right(t))
    case Bind(id2, _) if id == id2 => Some(Right(e))
    case Bind(id2, _) =>
      if (id2.isFreeIn(t))
        rc.reporter.fatalError(
          s"""Replacing ${Printer.asString(id)} by ${Printer.asString(t)} in
            |${Printer.asString(e)} would capture variable ${Printer.asString(id2)}""".stripMargin
        )
      else None
    case _ => None
  }).toOption.get

  def replace(id: Identifier, id2: Identifier)(implicit rc: RunContext): Tree = replace(id, Var(id2))

  def erase()(implicit rc: RunContext): Tree = extraction.Erasure.erase(this)
}
