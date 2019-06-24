package trees

import stainless.annotation._
import stainless.collection._
import stainless.lang._

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

case class Tuple(s: List[Tree]) extends Tree

case class TupleSelect(t: Tree, i: BigInt) extends Tree

case class Fix(body: Bind) extends Tree

case class Match(t: Tree, t1: Tree, t2: Bind) extends Tree

case class EitherMatch(t: Tree, t1: Bind, t2: Bind) extends Tree

case class LeftTree(t: Tree) extends Tree

case class RightTree(t: Tree) extends Tree

case class LetIn(tp: Option[Tree], v: Tree, bind: Bind) extends Tree

case class Because(t1: Tree, t2: Tree) extends Tree

case class NatEq(n: Tree, m: Tree) extends Tree

case class NatLeq(n: Tree, m: Tree) extends Tree

case class Add(n: Tree, m: Tree) extends Tree

case class Mul(n: Tree, m: Tree) extends Tree

case class Fold(t: Tree)

case class Unfold(tp: Option[Tree], t: Tree)

case class  Err(t: Option[Tree])

case class Abs(a: Tree, t: Tree)

case class Primitive(op: String)

case class Inst(t1: Tree, t2: Tree)

case class Refl(t1: Tree, t2: Tree)


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

case class RecType(t: Type)

//case class RefinementByType(t: Tree, cond: Bind) extends Tree
