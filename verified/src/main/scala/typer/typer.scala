package interpreter

import _root_.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._

object typer {
  /*def inferType(e: Tree, context: HashMap[Tree, Tree]): Tree = {
    e match {
      case BottomTree => BottomType
      case UnitLiteral => UnitType
      case NatLiteral(_) => NatType
      case BoolLiteral(_) => BoolType
      case Add(t1, t2) =>
        (inferType(t1), inferType(t2)) match {
          case (NatType, NatType) => NatType
          case (_, _) => BottomType
        }
      case Mul(t1, t2) =>
        (inferType(t1), inferType(t2)) match {
          case (NatType, NatType) => NatType
          case (_, _) => BottomType
        }
      case NatLeq(t1, t2) =>
        (inferType(t1), inferType(t2)) match {
          case (NatType, NatType) => NatType
          case (_, _) => BottomType
        }
        case NatEq(t1, t2) =>
        (inferType(t1), inferType(t2)) match {
          case (NatType, NatType) => NatType
          case (_, _) => BottomType
        }
      case IfThenElse(c, e1, e2) =>
        val tc = inferType(c)
        val t1 = inferType(e1)
        val t2 = inferType(e2)
        if(tc && BoolType && t1 == t2) t1
        else BottomType
      case App(e1, e2) =>
        val t1 = inferType(e1)
        val t2 = inferType(e2)
        t1 match {
          case ArrowType(tArg, tBody) if tArg == tBody => tBody
          case _ => BottomType
        }
      case Tuple(s) =>
        val t: List[Tree] = s.map(inferType(_))
        if(t.exists(_ == BottomType)) BottomType
        else Tuple(t)
      case LeftTree(e) =>

    }
  }*/
}