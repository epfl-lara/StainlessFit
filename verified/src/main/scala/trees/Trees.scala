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

case class Identifier(id: Int, name: String)

sealed abstract class Tree

case class Var(id: Identifier) extends Tree

case class Bind(id: Identifier, body: Tree) extends Tree

case class NatLiteral(n: BigInt) extends Tree /*{
  require(n >= 0)
}*/

case class Succ(t: Tree) extends Tree

case object UnitLiteral extends Tree

case object BottomTree extends Tree

case class BoolLiteral(b: Boolean) extends Tree

case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree

case class Lambda(tp: Option[Tree], body: Tree) extends Tree

case class App(t1: Tree, t2: Tree) extends Tree

case class Pair(t1: Tree, t2: Tree) extends Tree

case class First(t: Tree) extends Tree

case class Second(t: Tree) extends Tree

case class Fix(tp: Option[Tree], body: Tree) extends Tree

case class Match(t: Tree, t1: Tree, t2: Tree) extends Tree

case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree

case class LeftTree(t: Tree) extends Tree

case class RightTree(t: Tree) extends Tree

case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree

case class Because(t1: Tree, t2: Tree) extends Tree

case class Fold(t: Tree) extends Tree

case class Unfold(tp: Option[Tree], t: Tree) extends Tree

case class ErrorTree(s: String, t: Option[Tree]) extends Tree

case class Abs(a: Tree, t: Tree) extends Tree

case class Primitive(op: Operator, args: List[Tree]) extends Tree

case class Inst(t1: Tree, t2: Tree) extends Tree

case class Refl(t1: Tree, t2: Tree) extends Tree


case object BottomType extends Tree

case object TopType extends Tree

case object UnitType extends Tree

case object BoolType extends Tree

case object NatType extends Tree

case class SigmaType(t1: Tree, t2: Tree) extends Tree

case class PiType(t1: Tree, t2: Tree) extends Tree

case class SumType(t1: Tree, t2: Tree) extends Tree

case class IntersectionType(t1: Tree, t2: Tree) extends Tree

case class UnionType(t1: Tree, t2: Tree) extends Tree

case class RefinementType(t1: Tree, t2: Tree) extends Tree

case class PolyForallType(t1: Tree, t2: Tree) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree

case class RecType(n: Identifier, t0: Tree, t: Tree) extends Tree

//case class RefinementByType(t: Tree, cond: Tree) extends Tree
