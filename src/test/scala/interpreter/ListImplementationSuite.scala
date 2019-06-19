import org.scalatest.FunSuite
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import _root_.trees._
import _root_.interpreter.Interpreter._

object ListTree {

  def listToTree(l: List[BigInt]): Tree = l match {
    case Nil() => LeftTree(UnitLiteral)
    case h::t => RightTree(Tuple(List(NatLiteral(h), listToTree(t))))
  }

  def treeToList(l: Tree): List[BigInt] = l match {
    case LeftTree(UnitLiteral) => List()
    case RightTree(Tuple(t)) =>
      val NatLiteral(n) = t.head
      n::treeToList(t.tail.head)
    case _ => List()
  }

  val nil = listToTree(List())

  val cons = Lambda(
    None(),
    Bind(
      Some(Var(None(), "x")),
      Lambda(
        None(),
        Bind(
          Some(Var(None(), "l")),
          RightTree(Tuple(List(Var(None(), "x"), Var(None(), "l"))))
        )
      )
    )
  )

  val tail = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), BottomTree),
        Bind(Some(Var(None(), "t")), TupleSelect(Var(None(), "t"), 1))
      )
    )
  )

  val head = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), BottomTree),
        Bind(Some(Var(None(), "t")), TupleSelect(Var(None(), "t"), 0))
      )
    )
  )

  val isEmpty = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), BoolLiteral(true)),
        Bind(None(), BoolLiteral(false))
      )
    )
  )

  private val lenBody = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), NatLiteral(0)),
        Bind(
          Some(Var(None(), "t")),
          Add(
            NatLiteral(1),
            App(
              App(Var(None(), "len"), UnitLiteral),
              App(tail, Var(None(), "l"))
            )
          )
        )
      )
    )
  )

  val len = Fix(Bind(Some(Var(None(), "len")), lenBody))

  private val map2Body = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), nil),
        Bind(
          Some(Var(None(), "t")),
          App(
            App(cons, App(Var(None(), "f"), App(head, Var(None(), "l")))),
            App(
              App(Var(None(), "map"), UnitLiteral),
              App(tail, Var(None(), "l"))
            )
          )
        )
      )
    )
  )

  private val map2 = Fix(Bind(Some(Var(None(), "map")), map2Body))
  val map = Lambda(None(), Bind(Some(Var(None(), "f")), map2))

  private val filterTail = App(
    App(Var(None(), "filter"), UnitLiteral),
    App(tail, Var(None(), "l"))
  )

  private val filter2Body = Lambda(
    None(),
    Bind(
      Some(Var(None(), "l")),
      EitherMatch(
        Var(None(), "l"),
        Bind(None(), nil),
        Bind(
          Some(Var(None(), "t")),
          IfThenElse(
            App(Var(None(), "f"), App(head, Var(None(), "l"))),
            App(
              App(cons, App(head, Var(None(), "l"))),
              filterTail
            ),
            App(
              App(Var(None(), "filter"), UnitLiteral),
              filterTail
            )
          )
        )
      )
    )
  )

  private val filter2 = Fix(Bind(Some(Var(None(), "filter")), filter2Body))
  val filter = Lambda(None(), Bind(Some(Var(None(), "f")), filter2))
}

class ListTreeTest extends FunSuite  {
  import ListTree._

  val l1: List[BigInt] = List(1, 2, 3)
  val l2: List[BigInt] = List(3, -6, 9, -1, -5)

  val t1 = listToTree(l1)
  val t2 = listToTree(l2)


  val cons3 = App(cons, NatLiteral(3))
  val successor = Lambda(None(),
    Bind(Some(Var(None(), "x")), Add(NatLiteral(1), Var(None(), "x")))
  )
  val isPositive = Lambda(None(),
    Bind(Some(Var(None(), "x")), NatLeq(NatLiteral(0), Var(None(), "x")))
  )

  val mapSuccessor = App(map, successor)
  val filterIsPositive = App(filter, isPositive)


  test("evaluate head of a list is correct and leads to bottom if empty list") {
    assert(evaluate(App(head, t1), 1000) == NatLiteral(l1.head))
    assert(evaluate(App(head, t2), 1000) == NatLiteral(l2.head))
    assert(evaluate(App(head, nil), 1000) == BottomTree)
  }

  test("evaluate tail of a list is correct and leads to bottom if empty list") {
    assert(evaluate(App(tail, t1), 1000) == listToTree(l1.tail))
    assert(evaluate(App(tail, t2), 1000) == listToTree(l2.tail))
    assert(evaluate(App(tail, nil), 1000) == BottomTree)
  }

  test("cons of list...") {
    assert(evaluate(App(cons3, t1), 1000) == listToTree(BigInt(3)::l1))
    assert(evaluate(App(cons3, t2), 1000) == listToTree(BigInt(3)::l2))
    assert(evaluate(App(cons3, nil), 1000) == listToTree(BigInt(3)::Nil()))
  }

  test("test is empty..."){
    assert(evaluate(App(isEmpty, t1), 1000) == BoolLiteral(l1.isEmpty))
    assert(evaluate(App(isEmpty, t2), 1000) == BoolLiteral(l2.isEmpty))
    assert(evaluate(App(isEmpty, nil), 1000) == BoolLiteral(true))
  }

  test("test len") {
    assert(evaluate(App(len, t1), 1000) == NatLiteral(l1.size))
    assert(evaluate(App(len, t2), 1000) == NatLiteral(l2.size))
    assert(evaluate(App(len, nil), 1000) == NatLiteral(0))
  }

  test("test map") {
    val f = mapSuccessor
    assert(evaluate(App(f, t1), 1000) == listToTree(l1.map(_ + 1)))
    assert(evaluate(App(f, t2), 1000) == listToTree(l2.map(_ + 1)))
    assert(evaluate(App(f, nil), 1000) == nil)
  }

  test("test filter") {
    val f = filterIsPositive
    assert(evaluate(App(f, t1), 1000) == listToTree(l1.filter(_ >= 0)))
    assert(evaluate(App(f, t2), 1000) == listToTree(l2.filter(_ >= 0)))
    assert(evaluate(App(f, nil), 1000) == nil)
  }
}