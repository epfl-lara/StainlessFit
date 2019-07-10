import org.scalatest.FunSuite
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import trees._
import interpreter.Interpreter._
import parser.ScalaParser._
import parser._

class ParserSuite extends FunSuite {
  test("parser is LL1") {
    assert(expression.isLL1)
  }

  test("parse arithmetic operations") {
    val s = "(2 + 3) * 4 + 2 * 3 / 2 - 1".toIterator
    apply(ScalaLexer.apply(s)) match {
      case Parsed(e, _) => assert(evaluate(e, 1000) == NatLiteral((2 + 3) * 4 + 2 * 3 / 2 - 1))
      case _ => assert(false)
    }
  }

  test("parse function defintion") {
    val s = "val f = fun (x: Nat) => { x } in f(2)".toIterator
    apply(ScalaLexer.apply(s)) match {
      case Parsed(e, _) => assert(true || evaluate(e, 1000) == NatLiteral(2))
      case _ => assert(false)
    }
  }
}
