package stainlessfit
package core
package extraction

import util.RunContext
import trees._
import parser.FitParser
import typechecker.ScalaDepSugar._

import Namer._

class Namer(implicit val rc: RunContext) extends Phase[Int] {

  def transform(t: Tree): (Tree, Int) = Namer.namer(t, builtInMap, 0)

}

object Namer {
  val builtInMap =
    (BuiltInIdentifiers.builtInIdentifiers ++ BuiltInIdentifiers.builtInTypeIdentifiers)
      .map(id => Identifier(0, id) -> Identifier(0, id)).toMap

  def namer(t: Tree, m: Map[Identifier, Identifier], max: Int): (Tree, Int) = {
    t match {
      case UnitLiteral => (t, max)
      case NatLiteral(_) => (t, max)
      case BooleanLiteral(_) => (t, max)
      case UnitType => (t, max)
      case NatType => (t, max)
      case BoolType => (t, max)
      case TopType => (t, max)
      case BottomType => (t, max)
      case Error(s, Some(t)) =>
        val (newT, max1) = namer(t, m, max)
        (Error(s, Some(newT)), max1)
      case Error(_, None) => (t, max)
      case Var(id) =>
        m.get(id) match {
          case None => throw new java.lang.Exception(s"Error in name resolution: undefined variable $id at position ${t.pos}")
          case Some(newId) => (Var(newId), max)
        }
      case IfThenElse(cond, t1, t2) =>
        val (newC, max1) = namer(cond, m, max)
        val (newT1, max2) = namer(t1, m, max1)
        val (newT2, max3) = namer(t2, m, max2)
        (IfThenElse(newC, newT1, newT2), max3)
      case App(t1, t2) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (App(newT1, newT2), max2)
      case Pair(t1, t2) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (Pair(newT1, newT2), max2)
      case Size(t) =>
        val (newT, max1) = namer(t, m, max)
        (Size(newT), max1)
      case First(t) =>
        val (newT, max1) = namer(t, m, max)
        (First(newT), max1)
      case Second(t) =>
        val (newT, max1) = namer(t, m, max)
        (Second(newT), max1)
      case LeftTree(t) =>
        val (newT, max1) = namer(t, m, max)
        (LeftTree(newT), max1)
      case RightTree(t) =>
        val (newT, max1) = namer(t, m, max)
        (RightTree(newT), max1)
      case Bind(y, e) =>
        val m1 = m.updated(y, Identifier(max, y.name))
        val (newE, max2) = namer(e, m1, max + 1)
        (Bind(Identifier(max, y.name), newE), max2)
      case Lambda(Some(tp), bind) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (Lambda(Some(newTp), newBind), max2)
      case Lambda(None, bind) =>
        val (newBind, max1) = namer(bind, m, max)
        (Lambda(None, newBind), max1)
      case ErasableLambda(tp, bind) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (ErasableLambda(newTp, newBind), max2)
      case Fix(Some(tp), bind) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (Fix(Some(newTp), newBind), max2)
      case Fix(None, bind) =>
        val (newBind, max1) = namer(bind, m, max)
        (Fix(None, newBind), max1)

      case LetIn(Some(tp), v, bind) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newV, max2) = namer(v, m, max1)
        val (newBind, max3) = namer(bind, m, max2)
        (LetIn(Some(newTp), newV, newBind), max3)
      case LetIn(None, v, bind) =>
        val (newV, max1) = namer(v, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (LetIn(None, newV, newBind), max2)
      case MacroTypeDecl(tpe, bind) =>
        val (newTpe, max1) = namer(tpe, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (MacroTypeDecl(newTpe, newBind), max2)
      case MacroTypeInst(v, args) =>
        val (newV, max1) = namer(v, m, max)
        val newArgs =
          args.scanLeft((true, (UnitLiteral: Tree, max1))) {
            case (cmax, (isTerm, arg)) =>
              (isTerm, namer(arg, m, cmax._2._2))
          }.tail
        (MacroTypeInst(newV.asInstanceOf[Var], newArgs.map(p => (p._1, p._2._1))), newArgs.last._2._2)

      case NatMatch(t, t0, bind) =>
        val (newT, max1) = namer(t, m, max)
        val (newT0, max2) = namer(t0, m, max1)
        val (newBind, max3) = namer(bind, m, max2)
        (NatMatch(newT, newT0, newBind), max3)
      case EitherMatch(t, bind1, bind2) =>
        val (newT, max1) = namer(t, m, max)
        val (newBind1, max2) = namer(bind1, m, max1)
        val (newBind2, max3) = namer(bind2, m, max2)
        (EitherMatch(newT, newBind1, newBind2), max3)
      case Primitive(op, t ::  Nil) =>
        val (newT, max1) = namer(t, m, max)
        (Primitive(op, newT ::  Nil), max1)
      case Primitive(op, t1 ::  t2 ::  Nil) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (Primitive(op, newT1 ::  newT2 ::  Nil), max2)
      case ErasableApp(t1, t2) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (ErasableApp(newT1, newT2), max2)
      case Fold(tp, t) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newT, max2) = namer(t, m, max1)
        (Fold(newTp, newT), max2)
      case Unfold(t, bind) =>
        val (newT,max1) = namer(t, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (Unfold(newT, newBind), max2)
      case UnfoldPositive(t, bind) =>
        val (newT,max1) = namer(t, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (UnfoldPositive(newT, newBind), max2)
      case Abs(bind) =>
        val (newBind, max1) = namer(bind, m, max)
        (Abs(newBind), max1)
      case TypeApp(abs, t) =>
        val (newAbs, max1) = namer(abs, m, max)
        val (newT, max2) = namer(t, m, max1)
        (TypeApp(newAbs, newT), max2)
      case SumType(t1, t2) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (SumType(newT1, newT2), max2)
      case PiType(t1, bind) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (PiType(newT1, newBind), max2)
      case SigmaType(t1, bind) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (SigmaType(newT1, newBind), max2)
      case IntersectionType(t1, bind) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (IntersectionType(newT1, newBind), max2)
      case RefinementType(t1, bind) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (RefinementType(newT1, newBind), max2)
      case RefinementByType(t1, bind) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (RefinementByType(newT1, newBind), max2)
      case RecType(n, bind) =>
        val (newN, max1) = namer(n, m, max)
        val (newBind, max2) = namer(bind, m, max1)
        (RecType(newN, newBind), max2)
      case PolyForallType(bind) =>
        val (newBind, max1) = namer(bind, m, max)
        (PolyForallType(newBind), max1)
      case EqualityType(t1, t2) =>
        val (newT1, max1) = namer(t1, m, max)
        val (newT2, max2) = namer(t2, m, max1)
        (EqualityType(newT1, newT2), max2)
      case FixWithDefault(tp, t, td) =>
        val (newTp, max1) = namer(tp, m, max)
        val (newT: Bind, max2) = namer(t, m, max1)
        val (newTd, max3) = namer(td, m, max2)
        (FixWithDefault(newTp, newT, newTd), max3)

      case _ => throw new java.lang.Exception(s"Function `namer` is not defined on tree: $t")
    }
  }
}
