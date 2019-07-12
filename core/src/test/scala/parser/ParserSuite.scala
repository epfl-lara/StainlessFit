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
}
