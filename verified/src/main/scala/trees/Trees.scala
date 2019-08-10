package trees

import stainless.annotation._
import stainless.collection._
import stainless.lang._


sealed abstract class Operator {
  def isNatToNatBinOp: Boolean = Operator.isNatToNatBinOp(this)

  def isNatToBoolBinOp: Boolean = Operator.isNatToBoolBinOp(this)

  def isNatBinOp: Boolean = Operator.isNatBinOp(this)

  def isBoolBinOp: Boolean = Operator.isBoolBinOp(this)

  def isBoolUnOp: Boolean = Operator.isBoolBinOp(this)

  def returnedType: Tree = Operator.returnedType(this)

  def operandsType: Tree = Operator.operandsType(this)

  def isBinOp: Boolean = Operator.isBinOp(this)

  def isUnOp: Boolean = Operator.isUnOp(this)
}

case object Not extends Operator {
  override def toString = "!"
}
case object And extends Operator {
  override def toString = "&&"
}
case object Or extends Operator {
  override def toString = "||"
}

case object Plus extends Operator {
  override def toString = "+"
}
case object Minus extends Operator {
  override def toString = "-"
}
case object Mul extends Operator {
  override def toString = "*"
}
case object Div extends Operator {
  override def toString = "/"
}

case object Eq extends Operator {
  override def toString = "=="
}
case object Neq extends Operator {
  override def toString = "!="
}
case object Lteq extends Operator {
  override def toString = "<="
}
case object Gteq extends Operator {
  override def toString = ">="
}
case object Lt extends Operator {
  override def toString = "<"
}
case object Gt extends Operator {
  override def toString = ">"
}

case object Nop extends Operator {
  override def toString = "-"
}


object Operator {
  def isNatToNatBinOp(op: Operator): Boolean = {
    op match {
      case Plus => true
      case Minus => true
      case Mul => true
      case Div => true
      case _ => false
    }
  }

  def isNatToBoolBinOp(op: Operator): Boolean = {
    op match {
      case Eq => true
      case Neq => true
      case Lteq => true
      case Gteq => true
      case Lt => true
      case Gt => true
      case _ => false
    }
  }

  def isNatBinOp(op: Operator): Boolean = {
    isNatToNatBinOp(op) || isNatToBoolBinOp(op)
  }

  def isBoolBinOp(op: Operator): Boolean = {
    op match {
      case And => true
      case Or => true
      case _ => false
    }
  }

  def isBoolUnOp(op: Operator): Boolean = {
    op match {
      case Not => true
      case _ => false
    }
  }

  def isBinOp(op: Operator): Boolean = {
    isNatBinOp(op) || isBoolBinOp(op)
  }

  def isUnOp(op: Operator): Boolean = {
    isBoolUnOp(op)
  }

  def returnedType(op: Operator): Tree = {
    if(isNatToNatBinOp(op)) return NatType
    else if(isNatToBoolBinOp(op)) return BoolType
    else if(isBoolBinOp(op)) return BoolType
    else if(isBoolUnOp(op)) return BoolType
    else return BottomType
  }

  def operandsType(op: Operator): Tree = {
    if(isNatBinOp(op)) return NatType
    else if(isBoolBinOp(op)) return BoolType
    else if(isBoolUnOp(op)) return BoolType
    else return BottomType
  }
}

object Tree {
  def setId(t: Tree, m: Map[Identifier, Identifier], max: Int): (Tree, Map[Identifier, Identifier], Int) = {
    t match {
      case Var(id) => (Var(m(id)), m, max)
      case IfThenElse(cond, t1, t2) =>
        val (newC, m1, max1) = setId(cond, m, max)
        val (newT1, m2, max2) = setId(t1, m1, max1)
        val (newT2, m3, max3) = setId(t2, m2, max2)
        (IfThenElse(newC, newT1, newT2), m3, max3)
      case App(t1, t2) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newT2, m2, max2) = setId(t2, m1, max1)
        (App(newT1, newT2), m2, max2)
      case Pair(t1, t2) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newT2, m2, max2) = setId(t2, m1, max1)
        (Pair(newT1, newT2), m2, max2)
      case First(t) =>
        val (newT, m1, max1) = setId(t, m, max)
        (First(newT), m1, max1)
      case Second(t) =>
        val (newT, m1, max1) = setId(t, m, max)
        (Second(newT), m1, max1)
      case LeftTree(t) =>
        val (newT, m1, max1) = setId(t, m, max)
        (LeftTree(newT), m1, max1)
      case RightTree(t) =>
        val (newT, m1, max1) = setId(t, m, max)
        (RightTree(newT), m1, max1)
      case Bind(y, e) =>
        val m1 = m.updated(y, Identifier(max, y.name))
        val (newE, m2, max2) = setId(e, m1, max + 1)
        (Bind(Identifier(max, y.name), newE), m, max2)
      case Lambda(Some(tp), bind) =>
        val (newTp, m1, max1) = setId(tp, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (Lambda(Some(newTp), newBind), m2, max2)
      case Lambda(None(), bind) =>
        val (newBind, m1, max1) = setId(bind, m, max)
        (Lambda(None(), newBind), m1, max1)
      case Fix(Some(Bind(n, tp)), Bind(_, bind)) =>
        val m1 = m.updated(n, Identifier(max, n.name))
        val newN = Identifier(max, n.name)
        val (newTp, m2, max2) = setId(tp, m1, max + 1)
        val (newBind, m3, max3) = setId(bind, m2, max2)
        (Fix(Some(Bind(newN, newTp)), Bind(newN, newBind)), m3, max3)
      case Fix(None(), bind) =>
        val (newBind, m1, max1) = setId(bind, m, max)
        (Fix(None(), newBind), m1, max1)
      case LetIn(Some(tp), v, bind) =>
        val (newTp, m1, max1) = setId(tp, m, max)
        val (newV, m2, max2) = setId(v, m1, max1)
        val (newBind, m3, max3) = setId(bind, m2, max2)
        (LetIn(Some(newTp), newV, newBind), m3, max3)
      case LetIn(None(), v, bind) =>
        val (newV, m1, max1) = setId(v, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (LetIn(None(), newV, newBind), m2, max2)
      case Match(t, t0, bind) =>
        val (newT, m1, max1) = setId(t, m, max)
        val (newT0, m2, max2) = setId(t0, m1, max1)
        val (newBind, m3, max3) = setId(bind, m2, max2)
        (Match(newT, newT0, newBind), m3, max3)
      case EitherMatch(t, bind1, bind2) =>
        val (newT, m1, max1) = setId(t, m, max)
        val (newBind1, m2, max2) = setId(bind1, m1, max1)
        val (newBind2, m3, max3) = setId(bind2, m2, max2)
        (EitherMatch(newT, newBind1, newBind2), m3, max3)
      case Primitive(op, Cons(t, Nil())) =>
        val (newT, m1, max1) = setId(t, m, max)
        (Primitive(op, Cons(newT, Nil())), m1, max1)
      case Primitive(op, Cons(t1, Cons(t2, Nil()))) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newT2, m2, max2) = setId(t2, m1, max1)
        (Primitive(op, Cons(newT1, Cons(newT2, Nil()))), m2, max2)
      case Inst(t1, t2) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newT2, m2, max2) = setId(t2, m1, max1)
        (Inst(newT1, newT2), m2, max2)
      case Fold(Some(tp), t) =>
        val (newTp, m1, max1) = setId(tp, m, max)
        val (newT, m2, max2) = setId(t, m1, max1)
        (Fold(Some(newTp), newT), m2, max2)
      case Fold(None(), t) =>
        val (newT, m1, max1) = setId(t, m, max)
        (Fold(None(), newT), m1, max1)
      case Unfold(t, bind) =>
        val (newT, m1, max1) = setId(t, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (Unfold(newT, newBind), m2, max2)
      case UnfoldPositive(t, bind) =>
        val (newT, m1, max1) = setId(t, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (UnfoldPositive(newT, newBind), m2, max2)
      case Abs(bind) =>
        val (newBind, m1, max1) = setId(bind, m, max)
        (Abs(newBind), m1, max1)
      case TypeApp(abs, None()) =>
        val (newAbs, m1, max1) = setId(abs, m, max)
        (TypeApp(newAbs, None()), m1, max1)
      case TypeApp(abs, Some(t)) =>
        val (newAbs, m1, max1) = setId(abs, m, max)
        val (newT, m2, max2) = setId(t, m1, max1)
        (TypeApp(newAbs, Some(newT)), m2, max2)
      case SumType(t1, t2) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newT2, m2, max2) = setId(t2, m1, max1)
        (SumType(newT1, newT2), m2, max2)
      case PiType(t1, bind) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (PiType(newT1, newBind), m2, max2)
      case SigmaType(t1, bind) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (SigmaType(newT1, newBind), m2, max2)
      case IntersectionType(t1, bind) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (IntersectionType(newT1, newBind), m2, max2)
      case RefinementType(t1, bind) =>
        val (newT1, m1, max1) = setId(t1, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (RefinementType(newT1, newBind), m2, max2)
      case RecType(n, bind) =>
        val (newN, m1, max1) = setId(n, m, max)
        val (newBind, m2, max2) = setId(bind, m1, max1)
        (RecType(newN, newBind), m2, max2)
      case PolyForallType(bind) =>
        val (newBind, m1, max1) = setId(bind, m, max)
        (PolyForallType(newBind), m1, max1)
      case _ => (t, m, max)
    }
  }

  def replaceBind(bind: Tree, v: Tree): Tree = {
    require(isBind(bind))
    bind match {
      case Bind(id, body) => replace(id, v, body)
      case t => t
    }
  }

  def replace(xvar: Identifier, v: Tree, body: Tree): Tree = {
    body match {
      case Var(yvar) if yvar == xvar => v
      case Var(_) => body
      case UnitLiteral => body
      case NatLiteral(_) => body
      case BoolLiteral(_) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(replace(xvar, v, cond), replace(xvar, v, t1), replace(xvar, v, t2))
      case App(t1, t2) =>
        App(replace(xvar, v, t1), replace(xvar, v, t2))
      case Pair(t1, t2) => Pair(replace(xvar, v, t1), replace(xvar, v, t2))
      case First(t) => First(replace(xvar, v, t))
      case Second(t) => Second(replace(xvar, v, t))
      case LeftTree(t) => LeftTree(replace(xvar, v, t))
      case RightTree(t) => RightTree(replace(xvar, v, t))
      case Because(t1, t2) => Because(replace(xvar, v, t1), replace(xvar, v, t2))
      case Bind(yvar, e) if (xvar == yvar) => body
      case Bind(yvar, e) => Bind(yvar, replace(xvar, v, e))
      case Lambda(None(), bind) => Lambda(None(), replace(xvar, v, bind))
      case Lambda(Some(tp), bind) => Lambda(Some(replace(xvar, v, tp)), replace(xvar, v, bind))
      case Fix(None(), bind) => Fix(None(), replace(xvar, v, bind))
      case Fix(Some(tp), bind) => Fix(Some(replace(xvar, v, tp)), replace(xvar, v, bind))
      case LetIn(None(), v1, bind) => LetIn(None(), replace(xvar, v, v1), replace(xvar, v, bind))
      case LetIn(Some(tp), v1, bind) => LetIn(Some(replace(xvar, v, tp)), replace(xvar, v, v1), replace(xvar, v, bind))
      case Match(t, t0, bind) => Match(replace(xvar, v, t), replace(xvar, v, t0), replace(xvar, v, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replace(xvar, v, t), replace(xvar, v, bind1), replace(xvar, v, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replace(xvar, v, _)))
      case Inst(t1, t2) => Inst(replace(xvar, v, t1), replace(xvar, v, t2))
      case Fold(None(), t) => Fold(None(), replace(xvar, v, t))
      case Fold(Some(tp), t) => Fold(Some(replace(xvar, v, tp)), replace(xvar, v, t))
      case Unfold(t, bind) => Unfold(replace(xvar, v, t), replace(xvar, v, bind))
      case UnfoldPositive(t, bind) => UnfoldPositive(replace(xvar, v, t), replace(xvar, v, bind))
      case Abs(bind) => Abs(replace(xvar, v, bind))
      case TypeApp(abs, None()) => TypeApp(replace(xvar, v, abs), None())
      case TypeApp(abs, Some(t)) => TypeApp(replace(xvar, v, abs), Some(replace(xvar, v, t)))
      case ErrorTree(_, _) => body

      case NatType => body
      case BoolType => body
      case UnitType => body
      case SumType(t1, t2) => SumType(replace(xvar, v, t1), replace(xvar, v, t2))
      case PiType(t1, bind) => PiType(replace(xvar, v, t1), replace(xvar, v, bind))
      case SigmaType(t1, bind) => SigmaType(replace(xvar, v, t1), replace(xvar, v, bind))
      case IntersectionType(t1, bind) => IntersectionType(replace(xvar, v, t1), replace(xvar, v, bind))
      case RefinementType(t1, bind) => RefinementType(replace(xvar, v, t1), replace(xvar, v, bind))
      case RecType(n, bind) => RecType(replace(xvar, v, n), replace(xvar, v, bind))
      case PolyForallType(bind) => PolyForallType(replace(xvar, v, bind))
      case _ => throw new java.lang.Exception(s"Function replace is not implemented on $body (${body.getClass}).")
    }
  }

  def erase(t: Tree): Tree = t match {
    case Var(_) => t
    case UnitLiteral => t
    case NatLiteral(_) => t
    case BoolLiteral(_) => t
    case IfThenElse(cond, t1, t2) => IfThenElse(erase(cond), erase(t1), erase(t2))
    case App(t1, t2) => App(erase(t1), erase(t2))
    case Pair(t1, t2) => Pair(erase(t1), erase(t2))
    case First(t) => First(erase(t))
    case Second(t) => Second(erase(t))
    case LeftTree(t) => LeftTree(erase(t))
    case RightTree(t) => RightTree(erase(t))
    case Because(t1, t2) => Because(erase(t1), erase(t2))
    case Bind(yvar, e) => Bind(yvar, erase(e))
    case Lambda(_, bind) => Lambda(None(), erase(bind))
    case Fix(_, bind) => Fix(None(), erase(bind))
    case LetIn(_, v1, bind) => LetIn(None(), erase(v1), erase(bind))
    case Match(t, t0, bind) => Match(erase(t), erase(t0), erase(bind))
    case EitherMatch(t, bind1, bind2) => EitherMatch(erase(t), erase(bind1), erase(bind2))
    case Primitive(op, args) => Primitive(op, args.map(erase(_)))
    case Inst(t1, t2) => erase(t1)
    case Fold(_, t) => Fold(None(), erase(t))
    case Unfold(t, bind) => Unfold(erase(t), erase(bind))
    case UnfoldPositive(t, bind) => Unfold(erase(t), erase(bind))
    case Abs(bind) => Abs(erase(bind))
    case TypeApp(abs, _) => TypeApp(erase(abs), None())
    case ErrorTree(s, _) => ErrorTree(s, None())
    case _ => throw new java.lang.Exception(s"Function erase is not implemented on $t (${t.getClass}).")
  }

  def isError(e: Tree): Boolean = {
    decreases(e)
    e match {
      case ErrorTree(_, _) => true
      case _ => false
    }
  }

  def isValue(e: Tree): Boolean = {
    decreases(e)
    e match {
      case UnitLiteral => true
      case NatLiteral(_) => true
      case BoolLiteral(_) => true
      case Var(_) => true
      case Lambda(_, _) => true
      case Pair(t1, t2) => isValue(t1) && isValue(t2)
      case RightTree(t) => isValue(t)
      case LeftTree(t) => isValue(t)
      case Fold(_, t) => isValue(t)
      case Abs(_) => true
      case _ => false
    }
  }

  def isBind(t: Tree): Boolean = t.isInstanceOf[Bind]

  def isEvidentSubType(ty1: Tree, ty2: Tree): Boolean = {
    (ty1, ty2) match {
      case (BottomType, _) => true
      case (_, TopType) => true
      case (ty1, ty2) if ty1 == ty2 => true
      case (RefinementType(ty, Bind(a, t)), ty2) => isEvidentSubType(ty, ty2)
      case (SumType(l1, r1), SumType(l2, r2)) => isEvidentSubType(l1, l2) && isEvidentSubType(r1, r2)
      case (SigmaType(l1, Bind(x, r1)), SigmaType(l2, Bind(y, r2))) =>
        isEvidentSubType(l1, l2) && isEvidentSubType(r1, r2.replace(y, Var(x)))
      case (PiType(ty1, Bind(x, ty1b)), PiType(ty2, Bind(y, ty2b))) =>
        isEvidentSubType(ty2, ty1) && isEvidentSubType(ty1b, ty2b.replace(y, Var(x)))
      case (IntersectionType(ty1, Bind(x, ty1b)), IntersectionType(ty2, Bind(y, ty2b))) =>
        isEvidentSubType(ty2, ty1) && isEvidentSubType(ty2b, ty1b.replace(y, Var(x)))
      case (PolyForallType(Bind(x1, ty1)), PolyForallType(Bind(x2, ty2))) =>
        isEvidentSubType(ty1, ty2.replace(x2, Var(x1)))
      case _ => false
    }
  }

  def isType(t: Tree): Boolean = {
    t match {
      case NatType => true
      case BoolType => true
      case BottomType => true
      case TopType => true
      case UnitType => true
      case RefinementType(_, _) => true
      case SumType(_, _) => true
      case PiType(_, _) => true
      case IntersectionType(_, _) => true
      case RecType(_, _) => true
      case PolyForallType(_) => true
      case UnionType(_, _) => true
      case EqualityType(_, _) => true
      case SingletonType(_) => true
      case _ => false
    }
  }

  def isEqual(t1: Tree, t2: Tree): Boolean = {
    (t1, t2) match {
      case (IfThenElse(cond1, t11, t12), IfThenElse(cond2, t21, t22)) =>
        isEqual(cond1, cond2) && isEqual(t11, t21) && isEqual(t12, t22)
      case (App(t11, t12), App(t21, t22)) => isEqual(t11, t21) && isEqual(t12, t22)
      case (Pair(t11, t12), Pair(t21, t22)) => isEqual(t11, t21) && isEqual(t12, t22)
      case (First(t1), First(t2)) => isEqual(t1, t2)
      case (Second(t1), Second(t2)) => isEqual(t1, t2)
      case (LeftTree(t1), LeftTree(t2)) => isEqual(t1, t2)
      case (RightTree(t1), RightTree(t2)) => isEqual(t1, t2)
      case (Because(t11, t12), Because(t21, t22)) => isEqual(t11, t21) && isEqual(t12, t22)
      case (Bind(x1, t1), Bind(x2, t2)) => isEqual(t1, t2.replace(x2, Var(x1)))
      case (Lambda(_, bind1), Lambda(_, bind2)) => isEqual(bind1, bind2)
      case (Fix(_, bind1), Fix(_, bind2)) => isEqual(bind1, bind2)
      case (LetIn(_, v1, bind1), LetIn(_, v2, bind2)) => isEqual(v1, v2) && isEqual(bind1, bind2)
      case (Match(n1, t1, bind1), Match(n2, t2, bind2)) => isEqual(n1, n2) && isEqual(t1, t2) && isEqual(bind1, bind2)
      case (EitherMatch(t1, bind11, bind12), EitherMatch(t2, bind21, bind22)) =>
        isEqual(t1, t2) && isEqual(bind11, bind21) && isEqual(bind12, bind22)
      case (Primitive(op1, args1), Primitive(op2, args2)) =>
        if(op1 == op2 && args1.size == args2.size) args1.zip(args2).forall { case (t1, t2) => isEqual(t1, t2)}
        else false
      case (Inst(t11, t12), Inst(t21, t22)) => isEqual(t11, t21) && isEqual(t12, t22)
      case (Fold(_, t1), Fold(_, t2)) => isEqual(t1, t2)
      case (Unfold(t1, bind1), Unfold(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (UnfoldPositive(t1, bind1), UnfoldPositive(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (Abs(bind1), Abs(bind2)) => isEqual(bind1, bind2)
      case (TypeApp(abs1, Some(t1)), TypeApp(abs2, Some(t2))) => isEqual(abs1, abs2) && isEqual(t1, t2)
      case (TypeApp(abs1, None()), TypeApp(abs2, None())) => isEqual(abs1, abs2)
      case (SumType(t1, bind1), SumType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (PiType(t1, bind1), PiType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (SigmaType(t1, bind1), SigmaType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (IntersectionType(t1, bind1), IntersectionType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (RefinementType(t1, bind1), RefinementType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (RecType(t1, bind1), RecType(t2, bind2)) => isEqual(t1, t2) && isEqual(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => isEqual(bind1, bind2)
      case _ => t1 == t2
    }
  }

  def hasEasySubstitution(t: Tree): Boolean = {
    t match {
      case IfThenElse(cond, t1, t2) =>
        hasEasySubstitution(cond) || hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case App(Lambda(_, _), _) => true
      case App(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case Pair(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case First(t) => hasEasySubstitution(t)
      case Second(t) => hasEasySubstitution(t)
      case LeftTree(t) => hasEasySubstitution(t)
      case RightTree(t) => hasEasySubstitution(t)
      case Because(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case Bind(_, t) => hasEasySubstitution(t)
      case Lambda(_, t) => hasEasySubstitution(t)
      case Fix(_, t) => hasEasySubstitution(t)
      case LetIn(_, t1, t2) => true
      case Match(t, t1, t2) => hasEasySubstitution(t) || hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case EitherMatch(t, t1, t2) => hasEasySubstitution(t) || hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case Primitive(op, args) => args.exists(hasEasySubstitution(_))
      case Inst(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case Fold(_, t) => hasEasySubstitution(t)
      case Unfold(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case UnfoldPositive(t1, t2) => hasEasySubstitution(t1) || hasEasySubstitution(t2)
      case Abs(t) => hasEasySubstitution(t)
      case TypeApp(Abs(_), _) => true
      case TypeApp(t, _) => hasEasySubstitution(t)
      case _ => false
    }
  }

  def applyEasySubstitution(t: Tree): Tree = {
    t match {
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(applyEasySubstitution(cond), applyEasySubstitution(t1), applyEasySubstitution(t2))
      case App(Lambda(_, bind), t) => replaceBind(bind, t)
      case App(t1, t2) => App(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case Pair(t1, t2) => Pair(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case First(t) => First(applyEasySubstitution(t))
      case Second(t) => Second(applyEasySubstitution(t))
      case LeftTree(t) => LeftTree(applyEasySubstitution(t))
      case RightTree(t) => RightTree(applyEasySubstitution(t))
      case Because(t1, t2) => Because(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case Bind(x, t) => Bind(x, applyEasySubstitution(t))
      case Lambda(tp, t) => Lambda(tp, applyEasySubstitution(t))
      case Fix(tp, t) => Fix(tp, applyEasySubstitution(t))
      case LetIn(tp, t1, t2) => replaceBind(applyEasySubstitution(t2), t1)
      case Match(t, t1, t2) => Match(applyEasySubstitution(t), applyEasySubstitution(t1), applyEasySubstitution(t2))
      case EitherMatch(t, t1, t2) => EitherMatch(applyEasySubstitution(t), applyEasySubstitution(t1), applyEasySubstitution(t2))
      case Primitive(op, args) => Primitive(op, args.map(applyEasySubstitution(_)))
      case Inst(t1, t2) => Inst(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case Fold(tp, t) => Fold(tp, applyEasySubstitution(t))
      case Unfold(t1, t2) => Unfold(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case UnfoldPositive(t1, t2) => UnfoldPositive(applyEasySubstitution(t1), applyEasySubstitution(t2))
      case Abs(t) => Abs(applyEasySubstitution(t))
      case TypeApp(Abs(t), _) => t
      case TypeApp(t, ty) => TypeApp(applyEasySubstitution(t), ty)
      case t => t
    }
  }

}

case class Identifier(id: Int, name: String) {
  override def toString: String = name.toString// + "#" + id.toString

  def isFreeIn(e: Tree): Boolean = {
    e match {
      case Var(id) if id == this => true
      case IfThenElse(cond, t1, t2) =>
        isFreeIn(t1) || isFreeIn(t2) ||
        isFreeIn(cond)
      case App(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case Pair(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case First(t) => isFreeIn(t)
      case Second(t) => isFreeIn(t)
      case LeftTree(t) => isFreeIn(t)
      case RightTree(t) => isFreeIn(t)
      case Bind(y, e) if (this == y) => false
      case Bind(_, t) => isFreeIn(t)
      case Lambda(tp, bind) => isFreeIn(bind) || isFreeIn(tp.getOrElse(UnitLiteral))
      case Fix(tp, Bind(n, bind)) => isFreeIn(bind) || isFreeIn(tp.getOrElse(UnitLiteral))
      case LetIn(tp, v, bind) => isFreeIn(bind) || isFreeIn(v) || isFreeIn(tp.getOrElse(UnitLiteral))
      case Match(t, t0, bind) =>
        isFreeIn(t) || isFreeIn(t0) || isFreeIn(bind)
      case EitherMatch(t, bind1, bind2) =>
        isFreeIn(bind1) || isFreeIn(bind2) ||
        isFreeIn(t)
      case Primitive(op, args) =>
        args.exists(isFreeIn(_))
      case Fold(tp, t) => isFreeIn(t) || isFreeIn(tp.getOrElse(UnitLiteral))
      case Unfold(t, bind) => isFreeIn(t) || isFreeIn(bind)
      case UnfoldPositive(t, bind) => isFreeIn(t) || isFreeIn(bind)
      case Abs(bind) => isFreeIn(bind)
      case Inst(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case TypeApp(abs, tp) => isFreeIn(abs) && isFreeIn(tp.getOrElse(UnitLiteral))
      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RecType(n, bind) => isFreeIn(n) || isFreeIn(bind)
      case PolyForallType(bind) => isFreeIn(bind)
      case _ => false
    }
  }
}

sealed abstract class Tree {
  def isBind: Boolean = Tree.isBind(this)

  def isError: Boolean = Tree.isError(this)

  def isValue: Boolean = Tree.isValue(this)

  def isEvidentSubType(ty: Tree): Boolean = Tree.isEvidentSubType(this, ty)

  def isEqual(t: Tree): Boolean = Tree.isEqual(this, t)

  def replace(id: Identifier, t: Tree): Tree = Tree.replace(id, t, this)

  def erase(): Tree = Tree.erase(this)

  def hasEasySubstitution: Boolean = Tree.hasEasySubstitution(this)

  def applyEasySubstitution: Tree = Tree.applyEasySubstitution(this)
}

case class Var(id: Identifier) extends Tree {
  override def toString: String = id.toString
}

case class NatLiteral(n: BigInt) extends Tree {
  //require(n >= 0)
  override def toString: String = n.toString
}

case class Succ(t: Tree) extends Tree

case object UnitLiteral extends Tree {
  override def toString: String = "unit"
}

case object BottomTree extends Tree {
  override def toString: String = "⊥"
}

case class BoolLiteral(b: Boolean) extends Tree {
   override def toString: String = b.toString
}

case class Bind(id: Identifier, body: Tree) extends Tree {
  private def bodyString(): String = {
    " => {\n  " + body.toString.replaceAll("\n", "\n  ") + "\n}"
  }

  override def toString: String = id.toString + bodyString()

  def toStringWithType(ty: Tree): String = {
    id.toString + ": " + ty.toString + bodyString()
  }
}

case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "if (" + cond.toString + ") {\n" +
    "  " + t1.toString.replaceAll("\n", "\n  ") + "\n" +
    "}" + "\n" +
    "else {" + "\n" +
    "  " + t2.toString.replaceAll("\n", "\n  ") + "\n" +
    "}"
  }
}

case class Lambda(tp: Option[Tree], body: Tree) extends Tree {
  override def toString: String = {
    body match {
      case Bind(x, b) =>
        tp match {
          case Some(ty) => "λ" + Bind(x, b).toStringWithType(ty)
          case _ => "λ" + Bind(x, b).toString
        }
      case _ => "<Missing bind in λ>"
    }
  }
}

case class App(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t1.toString + "(" + t2.toString + ")"
  }
}

case class Pair(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
     "(" + t1.toString + ", " + t2.toString + ")"
  }
}

case class First(t: Tree) extends Tree {
  override def toString: String = {
    "First(" + t.toString + ")"
  }
}

case class Second(t: Tree) extends Tree {
  override def toString: String = {
    "Second(" + t.toString + ")"
  }
}

case class Fix(tp: Option[Tree], bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(n1, Bind(x, body)) =>
        val tyString = tp match {
          case Some(Bind(n, ty)) => "[" + n.toString + " => " + ty.toString + "]"
          case _ => ""
        }
        "Fix" + tyString + "(\n" +
        "  " + n1.toString + ", " + Bind(x, body).toString.replaceAll("\n", "\n  ") +
        "\n)"
      case _ => s"<Missing bind in Fix($tp, $bind)>"
    }
  }
}

case class Match(t: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(n, tn) =>
        t.toString + "match {\n" +
        "  case 0 =>\n" +
        t1.toString.replaceAll("\n", "\n    ") + "\n"
        "  case " + n.toString + " =>\n" +
        tn.toString.replaceAll("\n", "\n    ") + "\n}"
      case _ => "<Missing bind in Match>"
    }
  }
}

case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    (t1, t2) match {
      case (Bind(x1, t1), Bind(x2, t2)) =>
        t.toString + "match {\n" +
        "  case Left(" + x1.toString + ") =>\n" +
        t1.toString.replaceAll("\n", "\n    ") + "\n"
        "  case Right(" + x2.toString + ") =>\n" +
        t2.toString.replaceAll("\n", "\n    ") + "\n}"
      case _ => "<Missing bind in EitherMatch>"
    }
  }
}

case class LeftTree(t: Tree) extends Tree {
  override def toString: String = {
    "Left(" + t.toString + ")"
  }
}

case class RightTree(t: Tree) extends Tree {
  override def toString: String = {
    "Right(" + t.toString + ")"
  }
}

case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree {
  override def toString: String = {
    body match {
      case Bind(x, t) =>
        val typeString = tp match {
            case Some(ty) => ": " + ty.toString
            case _ => ""
          }
        "val " + x.toString + typeString + " = " + v.toString + " in\n" +
        t.toString
      case _ => "<Missing bind in LetIn>"
    }
  }
}

case class ErrorTree(s: String, t: Option[Tree]) extends Tree {
  override def toString: String = t match {
    case None() => s"Error($s)"
    case Some(tp) => s"Error[$tp]($s)"
  }
}

case class Primitive(op: Operator, args: List[Tree]) extends Tree {
  override def toString: String = {
    args match {
      case Cons(n1, Nil()) => op.toString + "(" + n1.toString + ")"
      case Cons(n1, Cons(n2, Nil())) =>
        "(" + n1.toString + ")" + op.toString + "(" + n2.toString + ")"
      case _ => throw new java.lang.Exception("Primitive operations have one or two arguments.")
    }
  }
}

case class Inst(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "Inst(" + t1.toString + ", " + t2.toString + ")"
  }
}

case class Refl(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "Refl(" + t1.toString + ", " + t2.toString + ")"
  }
}

case class Fold(tp: Option[Tree], t: Tree) extends Tree {
  override def toString: String = {
    val typeString = tp match {
      case Some(ty) => "[" + ty.toString + "]"
      case _ => ""
    }
    "Fold(" + typeString + t.toString
  }
}

case class Unfold(t: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(_, _) => "Unfold " + t.toString + " in " + bind.toString + ")"
      case _ => "<Missing bind in Unfold>"
    }
  }
}

case class UnfoldPositive(t: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(_, _) => "UnfoldPositive " + t.toString + " in " + bind.toString + ")"
      case _ => "<Missing bind in UnfoldPositive>"
    }
  }
}

case class Abs(t: Tree) extends Tree {
  override def toString: String = {
    t match {
      case Bind(a, t) =>
        "Λ" + a.toString + ". " + t.toString
      case _ => "<Missing bind in Abs>"
    }
  }
}

case class TypeApp(t1: Tree, t2: Option[Tree]) extends Tree {
  override def toString: String = {
    val t2S = t2 match {
      case Some(t) => t.toString
      case _ => ""
    }
    t1.toString + "[" + t2S + "]"
  }
}

case object BottomType extends Tree {
  override def toString: String = "⊥"
}

case object TopType extends Tree {
  override def toString: String = "⊤"
}

case object UnitType extends Tree {
  override def toString: String = "Unit"
}

case object BoolType extends Tree {
  override def toString: String = "Bool"
}

case object NatType extends Tree {
  override def toString: String = "Nat"
}

case class SigmaType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(Σ" + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in SigmaType>"
    }
  }
}

case class SumType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "(" + t1.toString + ") + (" + t2.toString + ")"
  }
}

case class PiType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(Π " + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in PiType>"
    }
  }
}

case class IntersectionType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(∀" + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in IntersectionType>"
    }
  }
}

case class RefinementType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "{" + x.toString + ": " + t1.toString + ", " + t2.toString + "}"
      case _ => "<Missing bind in RefinementType>"
    }
  }
}

case class RecType(n: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(a, ty) =>
        "(Rec(" + n.toString + ")(" + a.toString + " => " + ty.toString + ")"
      case _ => "<Missing bind in RecType>"
    }
  }
}

case class PolyForallType(t: Tree) extends Tree {
  override def toString: String = {
    t match {
      case Bind(a, t) =>
        "(∀" + a.toString + ": Type. " + t.toString
      case _ => "<Missing bind in PolyForallType>"
    }
  }
}


case class UnionType(t1: Tree, t2: Tree) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree




case class Because(t1: Tree, t2: Tree) extends Tree


//case class RefinementByType(t: Tree, cond: Tree) extends Tree
