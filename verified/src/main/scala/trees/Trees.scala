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
      case SumType(t1, t2) => SumType(replace(xvar, v, t1), replace(xvar, v, t2))
      case PiType(t1, bind) => PiType(replace(xvar, v, t1), replace(xvar, v, bind))
      case SigmaType(t1, bind) => SigmaType(replace(xvar, v, t1), replace(xvar, v, bind))
      case IntersectionType(t1, bind) => IntersectionType(replace(xvar, v, t1), replace(xvar, v, bind))
      case RefinementType(t1, bind) => RefinementType(replace(xvar, v, t1), replace(xvar, v, bind))
      case RecType(n, bind) => RecType(replace(xvar, v, n), replace(xvar, v, bind))
      case _ => body
    }
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
      case _ => false
    }
  }

  def isBind(t: Tree): Boolean = t.isInstanceOf[Bind]

  def isEvidentSubType(ty1: Tree, ty2: Tree): Boolean = {
    (ty1, ty2) match {
      case (BottomType, _) => true
      case (ty1, ty2) if ty1 == ty2 => true
      case (ty2, RefinementType(ty, Bind(a, t))) => isEvidentSubType(ty, ty2)
      case (SumType(l1, r1), SumType(l2, r2)) => isEvidentSubType(l1, l2) && isEvidentSubType(r1, r2)
      case (SigmaType(l1, Bind(x, r1)), SigmaType(l2, Bind(y, r2))) =>
        isEvidentSubType(l1, l2) && isEvidentSubType(r1, Tree.replace(y, Var(x), r2))
      case (PiType(ty1, Bind(x, ty1b)), PiType(ty2, Bind(y, ty2b))) =>
        isEvidentSubType(ty1, ty2) && isEvidentSubType(ty1b, Tree.replace(y, Var(x), ty2b))
      case (IntersectionType(ty1, Bind(x, ty1b)), IntersectionType(ty2, Bind(y, ty2b))) =>
        isEvidentSubType(ty1, ty2) && isEvidentSubType(ty2b, Tree.replace(y, Var(x), ty1b))
      case (RecType(n, Bind(x, ty1)), PiType(m, Bind(y, ty2))) =>
        n == m && isEvidentSubType(ty1, Tree.replace(y, Var(x), ty2))
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
}

case class Identifier(id: Int, name: String) {
  override def toString: String = name.toString + "#" + id.toString

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
      case Inst(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case _ => false
    }
  }
}

sealed abstract class Tree {
  def isBind: Boolean = Tree.isBind(this)

  def isError: Boolean = Tree.isError(this)

  def isValue: Boolean = Tree.isValue(this)
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
      case _ => "<No bind in λ>"
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

case class Fix(tp: Option[Tree], body: Tree) extends Tree {
  override def toString: String = {
    this match {
      case Fix(Some(Bind(n, ty)), Bind(n1, Bind(x, body))) =>
        val tyString = tp match {
          case Some(Bind(n, ty)) => "[" + n.toString + " => " + ty.toString + "]"
          case _ => ""
        }
        "Fix" + tyString + "(\n" +
        "  " + n1.toString + ", " + Bind(x, body).toString.replaceAll("\n", "\n  ") +
        "\n)"
      case _ => "<No bind in Fix>"
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
      case _ => "<No bind in Match>"
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
      case _ => "<No bind in EitherMatch>"
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
      case _ => "<No bind in LetIn>"
    }
  }
}


case class ErrorTree(s: String, t: Option[Tree]) extends Tree {
  override def toString: String = t match {
    case None() => s"Error($s)"
    case Some(tp) => s"Error[$tp]($s)"
  }
}

case class Abs(a: Tree, t: Tree) extends Tree

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
      case _ => "Missing bind in Fold>"
    }
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
      case _ => "<No bind in SigmaType>"
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
      case _ => "<No bind in PiType>"
    }
  }
}

case class IntersectionType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(∀" + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<No bind in IntersectionType>"
    }
  }
}

case class RefinementType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "{" + x.toString + ": " + t1.toString + ", " + t2.toString + "}"
      case _ => "<No bind in RefinementType>"
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

case class UnionType(t1: Tree, t2: Tree) extends Tree

case class PolyForallType(t1: Tree) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree




case class Because(t1: Tree, t2: Tree) extends Tree


//case class RefinementByType(t: Tree, cond: Tree) extends Tree
