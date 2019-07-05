import org.scalatest.FunSuite
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import _root_.trees._
import _root_.interpreter.Interpreter._

/*class InterpreterSuite extends FunSuite {

  def asVar(x: String): Var = {
    Var(None(), x)
  }

  val identity = Lambda(None(), Bind(Some(asVar("x")), asVar("x")))

  val facBody = Lambda(
    None(),
    Bind(
      Some(asVar("n")),
      Match(
        asVar("n"),
        NatLiteral(1),
        Bind(
          Some(asVar("m")),
          Mul(
            asVar("n"),
            App(App(asVar("fac"), UnitLiteral), asVar("m"))
          )
        )
      )
    )
  )
  val fac = Fix(Bind(Some(asVar("fac")), facBody))

  def facApp(n: BigInt): Tree = {
    App(fac, NatLiteral(n))
  }

  test("replace do not subsitute bind variables") {
    val f = Lambda(None(), Bind(Some(asVar("x")), asVar("x")))
    assert(f === replace(asVar("x"), NatLiteral(2), f))
  }

  test("replace iff same id and same name") {
    val x1 = Var(Some(1), "x")
    val x2 = Var(Some(2), "x")
    val y1 = Var(Some(1), "y")
    val y2 = Var(Some(2), "y")

    assert(replace(Var(Some(1), "x"), NatLiteral(2), x1) === NatLiteral(2))
    assert(replace(Var(Some(1), "x"), NatLiteral(2), x2) === x2)
    assert(replace(Var(Some(1), "x"), NatLiteral(2), y1) === y1)
    assert(replace(Var(Some(1), "x"), NatLiteral(2), y2) === y2)
  }

  test("replaceBind replace...") {
    val f = Bind(
      Some(asVar("x")),
      IfThenElse(NatLeq(asVar("x"), asVar("y")), asVar("x"), asVar("y"))
    )
    val f1 = IfThenElse(
      NatLeq(NatLiteral(2), asVar("y")),
      NatLiteral(2),
      asVar("y")
    )

    assert(replaceBind(f, NatLiteral(2)) == f1)
  }

  test("condition evaluation takes the correct branch") {
    val c1 = IfThenElse(BoolLiteral(true), NatLiteral(2), NatLiteral(3))
    val c2 = IfThenElse(BoolLiteral(false), NatLiteral(2), NatLiteral(3))
    assert(evaluate(c1, 1000) === NatLiteral(2))
    assert(evaluate(c2, 1000) === NatLiteral(3))
  }

  test("letIn evaluation leads to replacement") {
    val e = LetIn(None(), NatLiteral(4), Bind(Some(asVar("x")), asVar("x")))
    assert(evaluate(e, 1000) === NatLiteral(4))
  }

  test("tupleSelect evaluation") {
    val e = First(
      Second(
        Pair(BoolLiteral(true), Pair(BoolLiteral(false), NatLiteral(3)))
      )
    )
    assert(evaluate(e, 1000) === BoolLiteral(false))
  }

  test("app evaluation") {
    val n = App(identity, NatLiteral(2))
    assert(evaluate(n, 1000) === NatLiteral(2))
  }

  test("nested app evaluation") {
    val f = Lambda(None(), Bind(Some(asVar("x")), identity))
    val g = App(f, NatLiteral(2))
    val n = App(g, NatLiteral(3))
    assert(evaluate(g, 1000) === identity)
    assert(evaluate(n, 1000) === NatLiteral(3))
  }

  test("factorial evaluation") {
    assert(evaluate(facApp(0), 1000) == NatLiteral(1))
    assert(evaluate(facApp(3), 1000) == NatLiteral(6))
    assert(evaluate(facApp(6), 1000) == NatLiteral(720))
  }

  test("evaluate a tuple is equivalent to evaluate each of its element") {
    val tupleOfFac = Pair(facApp(0), Pair(facApp(1), facApp(2)))
    val tupleOfFacEvaluated = Pair(
      evaluate(facApp(0), 1000),
      Pair(evaluate(facApp(1), 1000), evaluate(facApp(2), 1000))
    )
    assert(evaluate(tupleOfFac, 1000) === tupleOfFacEvaluated)
  }

  test("select i-th element of tuple is evaluate the i-th element") {
    val tupleOfFac = Pair(facApp(0), Pair(facApp(1), facApp(2)))
    assert(evaluate(First(Second(tupleOfFac)), 1000) === evaluate(facApp(1), 1000))
  }
}*/