import trees._
import interpreter._
import printer._

object ListTree {

  def listToTree(l: List[Int]): Tree = l match {
    case Nil => Left(UnitLiteral)
    case h::t => Right(Tuple(Seq(NatLiteral(h), listToTree(t))))
  }

  def treeToList(l: Tree): List[BigInt] = l match {
    case Left(UnitLiteral) => List()
    case Right(Tuple(t)) =>
      val NatLiteral(n) = t.head
      n::treeToList(t.tail.head)
    case _ => List()
  }

  val nil = listToTree(List())

  val cons = Lambda(
    None,
    Bind(
      Some(Var(1, "x")),
      Lambda(
        None,
        Bind(
          Some(Var(1, "l")),
          Right(Tuple(Seq(Var(1, "x"), Var(1, "l"))))
        )
      )
    )
  )

  val tail = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, BottomTree),
        Bind(Some(Var(1, "t")), TupleSelect(Var(1, "t"), 1))
      )
    )
  )

  val head = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, BottomTree),
        Bind(Some(Var(1, "t")), TupleSelect(Var(1, "t"), 0))
      )
    )
  )

  val isEmpty = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, BoolLiteral(true)),
        Bind(None, BoolLiteral(false))
      )
    )
  )

  private val lenBody = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, NatLiteral(0)),
        Bind(
          Some(Var(1, "t")),
          Add(
            NatLiteral(1),
            App(
              App(Var(1, "len"), UnitLiteral),
              App(tail, Var(1, "l"))
            )
          )
        )
      )
    )
  )

  val len = Fix(Bind(Some(Var(1, "len")), lenBody))

  private val map2Body = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, nil),
        Bind(
          Some(Var(1, "t")),
          App(
            App(cons, App(Var(1, "f"), App(head, Var(1, "l")))),
            App(
              App(Var(1, "map"), UnitLiteral),
              App(tail, Var(1, "l"))
            )
          )
        )
      )
    )
  )

  private val map2 = Fix(Bind(Some(Var(1, "map")), map2Body))
  val map = Lambda(None, Bind(Some(Var(1, "f")), map2))

  private val filterTail = App(
    App(Var(1, "filter"), UnitLiteral),
    App(tail, Var(1, "l"))
  )

  private val filter2Body = Lambda(
    None,
    Bind(
      Some(Var(1, "l")),
      EitherMatch(
        Var(1, "l"),
        Bind(None, nil),
        Bind(
          Some(Var(1, "t")),
          IfThenElse(
            App(Var(1, "f"), App(head, Var(1, "l"))),
            App(
              App(cons, App(head, Var(1, "l"))),
              filterTail
            ),
            App(
              App(Var(1, "filter"), UnitLiteral),
              filterTail
            )
          )
        )
      )
    )
  )

  private val filter2 = Fix(Bind(Some(Var(1, "filter")), filter2Body))
  val filter = Lambda(None, Bind(Some(Var(1, "f")), filter2))
}

object ListTreeTest {
  import ListTree._
  import Interpreter._

  val l1 = List(1, 2, 3)
  val l2 = List(3, -6, 9, -1, -5)

  val t1 = listToTree(l1)
  val t2 = listToTree(l2)


  val cons3 = App(cons, NatLiteral(3))
  val successor = Lambda(None,
    Bind(Some(Var(1, "x")), Add(NatLiteral(1), Var(1, "x")))
  )
  val isPositive = Lambda(None,
    Bind(Some(Var(1, "x")), NatLeq(NatLiteral(0), Var(1, "x")))
  )

  val mapSuccessor = App(map, successor)
  val filterIsPositive = App(filter, isPositive)

  def run: Unit = {
    testHead
    testTail
    testCons
    testLen
    testMap
    testFilter
  }

  def testHead: Unit = {
    assert(evaluate(App(head, t1), 1000) == NatLiteral(l1.head))
    assert(evaluate(App(head, t2), 1000) == NatLiteral(l2.head))
    assert(evaluate(App(head, nil), 1000) == BottomTree)
  }

  def testTail: Unit = {
    assert(evaluate(App(tail, t1), 1000) == listToTree(l1.tail))
    assert(evaluate(App(tail, t2), 1000) == listToTree(l2.tail))
    assert(evaluate(App(tail, nil), 1000) == BottomTree)
  }

  def testCons: Unit = {
    assert(evaluate(App(cons3, t1), 1000) == listToTree(3::l1))
    assert(evaluate(App(cons3, t2), 1000) == listToTree(3::l2))
    assert(evaluate(App(cons3, nil), 1000) == listToTree(3::Nil))
  }

  def testIsEmpty: Unit = {
    assert(evaluate(App(isEmpty, t1), 1000) == BoolLiteral(l1.isEmpty))
    assert(evaluate(App(isEmpty, t2), 1000) == BoolLiteral(l2.isEmpty))
    assert(evaluate(App(isEmpty, nil), 1000) == BoolLiteral(true))
  }

  def testLen: Unit = {
    assert(evaluate(App(len, t1), 1000) == NatLiteral(l1.size))
    assert(evaluate(App(len, t2), 1000) == NatLiteral(l2.size))
    assert(evaluate(App(len, nil), 1000) == NatLiteral(0))
  }

  def testMap: Unit = {
    val f = mapSuccessor
    assert(evaluate(App(f, t1), 1000) == listToTree(l1.map(_ + 1)))
    assert(evaluate(App(f, t2), 1000) == listToTree(l2.map(_ + 1)))
    assert(evaluate(App(f, nil), 1000) == nil)
  }

  def testFilter: Unit = {
    val f = filterIsPositive
    assert(evaluate(App(f, t1), 1000) == listToTree(l1.filter(_ >= 0)))
    assert(evaluate(App(f, t2), 1000) == listToTree(l2.filter(_ >= 0)))
    assert(evaluate(App(f, nil), 1000) == nil)
  }
}

object InterpreterTest {
  import Interpreter._

  val facBody = Lambda(
    None,
    Bind(
      Some(Var(1, "n")),
      Match(
        Var(1, "n"),
        NatLiteral(1),
        Bind(
          Some(Var(1, "m")),
          Mul(
            Var(1, "n"),
            App(
              App(Var(1, "fac"), UnitLiteral),
              Var(1, "m")
            )
          )
        )
      )
    )
  )
  val fac = Fix(Bind(Some(Var(1, "fac")), facBody))

  def run: Unit = {
    testReplacement
    testCondition
    testTuple
  }

  def testReplacement: Unit = {
    val f = Lambda(
      None,
      Bind(
        Some(Var(1, "x")),
        Lambda(
          None,
          Bind(
            Some(Var(1, "y")),
            Var(1, "y")
          )
        )
      )
    )
    val x = evaluate(App(App(f, NatLiteral(2)), NatLiteral(3)), 1000)
    assert(x == NatLiteral(3))
  }

  def testCondition: Unit = {
    val c1 = IfThenElse(BoolLiteral(true), NatLiteral(2), NatLiteral(3))
    val c2 = IfThenElse(BoolLiteral(false), NatLiteral(2), NatLiteral(3))
    assert(evaluate(c1, 1000) == NatLiteral(2))
    assert(evaluate(c2, 1000) == NatLiteral(3))
  }

  def testTuple: Unit = {
    val e1 = TupleSelect(
      Tuple(Seq(BoolLiteral(true), BoolLiteral(false), NatLiteral(3))),
      2
    )
    val e2 = TupleSelect(
      Tuple(
        Seq(
          App(fac, NatLiteral(1)),
          App(fac, NatLiteral(2)),
          App(fac, NatLiteral(3)),
          App(fac, NatLiteral(4)),
          App(fac, NatLiteral(5))
        ),
      ),
      3
    )
    assert(evaluate(e1, 1000) == NatLiteral(3))
    assert(evaluate(e2, 1000) == evaluate(App(fac, NatLiteral(4)), 1000))
  }

  def testLetIn: Unit = {
    val e = LetIn(None, NatLiteral(4), Bind(Some(Var(1, "x")), App(fac, Var(1, "x"))))
    assert(evaluate(e, 1000) == evaluate(App(fac, NatLiteral(4)), 1000))
  }


}
object Main {
  def main(args: Array[String]): Unit = {
    ListTreeTest.run
    InterpreterTest.run
  }
}
