package trees

import stainless.annotation._
import stainless.collection._
import stainless.lang._


sealed abstract class Operator

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
        (Bind(Identifier(max, y.name), newE), m2, max2)
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
        (Inst(newT1, newT2), m2, max2)/*
      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)*/
      case _ => (t, m, max)
    }
  }

  /*def appearsFreeIn(v: Identifier, e: Tree): Boolean = {
    e match {
      case Var(id) if id == v => true
      case IfThenElse(cond, t1, t2) =>
        appearsFreeIn(v, t1) || appearsFreeIn(v, t2) ||
        appearsFreeIn(v, cond)
      case App(t1, t2) => appearsFreeIn(v, t1) || appearsFreeIn(v, t2)
      case Pair(t1, t2) => appearsFreeIn(v, t1) || appearsFreeIn(v, t2)
      case First(t) => appearsFreeIn(v, t)
      case Second(t) => appearsFreeIn(v, t)
      case LeftTree(t) => appearsFreeIn(v, t)
      case RightTree(t) => appearsFreeIn(v, t)
      case Bind(yvar, e) if (v == Var(yvar)) => false
      case Bind(_, t) => appearsFreeIn(v, t)

      case Lambda(tp, bind) => appearsFreeIn(v, bind)
      case Fix(tp, Bind(n, bind)) => appearsFreeIn(v, bind)
      case LetIn(tp, v1, bind) => appearsFreeIn(v, bind)
      case Match(t, t0, bind) =>
        appearsFreeIn(v, t) || appearsFreeIn(v, t0) ||
        appearsFreeIn(v, bind)
      case EitherMatch(t, bind1, bind2) =>
        appearsFreeIn(v, bind1) || appearsFreeIn(v, bind2) ||
        appearsFreeIn(v, t)
      case Primitive(op, args) =>
        args.exists(appearsFreeIn(v, _))
      case Inst(t1, t2) => appearsFreeIn(v, t1) || appearsFreeIn(v, t2)
      case SumType(t1, t2) => appearsFreeIn(v, t1) || appearsFreeIn(v, t2)
      case PiType(t1, bind) => appearsFreeIn(v, t1) || appearsFreeIn(v, bind)
      case SigmaType(t1, bind) => appearsFreeIn(v, t1) || appearsFreeIn(v, bind)
      case IntersectionType(t1, bind) => appearsFreeIn(v, t1) || appearsFreeIn(v, bind)
      case RefinementType(t1, bind) => appearsFreeIn(v, t1) || appearsFreeIn(v, bind)
      case _ => false
    }
  }*/

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
      case Lambda(tp, bind) => isFreeIn(bind)
      case Fix(tp, Bind(n, bind)) => isFreeIn(bind)
      case LetIn(tp, this1, bind) => isFreeIn(bind)
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

sealed abstract class Tree

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
    "if(" + cond.toString + ") {\n" +
    "  " + t1.toString.replaceAll("\n", "\n  ") + "\n" +
    "}" +
    "else {" +
    "  " + t2.toString.replaceAll("\n", "\n  ") + "\n"
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
      case Fix(Some(Bind(n, ty)), Bind(_, Bind(x, body))) =>
        "Fix[" + n.toString + " => " + ty.toString + "](\n" +
        "  " + n.toString + ", " + Bind(x, body).toString.replaceAll("\n", "\n  ") +
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
  override def toString: String = {
    "Error(" + s + ")"
  }
}

case class Abs(a: Tree, t: Tree) extends Tree

case class Primitive(op: Operator, args: List[Tree]) extends Tree {
  override def toString: String = {
    args match {
      case Cons(n1, Nil()) => op.toString + "(" + n1.toString + ")"
      case Cons(n1, Cons(n2, Nil())) =>
        "(" + n1.toString + ")" + op.toString + "(" + n2.toString + ")"
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
      case _ => "<No bind in PiType>"
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

case class UnionType(t1: Tree, t2: Tree) extends Tree

case class PolyForallType(t1: Tree) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree

case class RecType(n: Identifier, t0: Tree, t: Tree) extends Tree



case class Because(t1: Tree, t2: Tree) extends Tree

case class Fold(t: Tree) extends Tree

case class Unfold(tp: Option[Tree], t: Tree) extends Tree


//case class RefinementByType(t: Tree, cond: Tree) extends Tree
