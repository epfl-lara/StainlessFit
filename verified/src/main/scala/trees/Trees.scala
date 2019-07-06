package trees

import stainless.annotation._
import stainless.collection._
import stainless.lang._


sealed abstract class Operator

case object Not extends Operator
case object And extends Operator
case object Or extends Operator

case object Plus extends Operator
case object Minus extends Operator
case object Mul extends Operator
case object Div extends Operator

case object Eq extends Operator
case object Neq extends Operator
case object Lteq extends Operator
case object Gteq extends Operator
case object Lt extends Operator
case object Gt extends Operator

case object Nop extends Operator


sealed abstract class Tree

case class Var(id: Option[Int], name: String) extends Tree

case class Bind(x: Option[Var], body: Tree) extends Tree

case class NatLiteral(n: BigInt) extends Tree /*{
  require(n >= 0)
}*/

case object UnitLiteral extends Tree

case object BottomTree extends Tree

case class BoolLiteral(b: Boolean) extends Tree

case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree

case class Lambda(tp: Option[Tree], body: Bind) extends Tree

case class App(t1: Tree, t2: Tree) extends Tree

case class Pair(t1: Tree, t2: Tree) extends Tree

case class First(t: Tree) extends Tree

case class Second(t: Tree) extends Tree

case class Fix(body: Bind) extends Tree

case class Match(t: Tree, t1: Tree, t2: Bind) extends Tree

case class EitherMatch(t: Tree, t1: Bind, t2: Bind) extends Tree

case class LeftTree(t: Tree) extends Tree

case class RightTree(t: Tree) extends Tree

case class LetIn(tp: Option[Tree], v: Tree, bind: Bind) extends Tree

case class Because(t1: Tree, t2: Tree) extends Tree

case class Fold(t: Tree) extends Tree

case class Unfold(tp: Option[Tree], t: Tree) extends Tree

case class Err(t: Option[Tree]) extends Tree

case class Abs(a: Tree, t: Tree) extends Tree

case class Primitive(op: Operator, args: List[Tree]) extends Tree

case class Inst(t1: Tree, t2: Tree) extends Tree

case class Refl(t1: Tree, t2: Tree) extends Tree


case object BottomType extends Tree

case object TopType extends Tree

case object UnitType extends Tree

case object BoolType extends Tree

case object NatType extends Tree

case class SigmaType(t1: Tree, t2: Bind) extends Tree

case class PiType(t1: Tree, t2: Bind) extends Tree

case class SumType(t1: Tree, t2: Tree) extends Tree

case class IntersectionType(t1: Tree, t2: Bind) extends Tree

case class UnionType(t1: Tree, t2: Bind) extends Tree

case class RefinementType(t1: Tree, t2: Bind) extends Tree

case class PolyForallType(t: Bind) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree

case class RecType(n: Tree, t0: Tree, t: Bind) extends Tree

//case class RefinementByType(t: Tree, cond: Bind) extends Tree
