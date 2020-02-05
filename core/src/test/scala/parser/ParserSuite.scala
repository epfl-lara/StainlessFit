package stainlessfit

import org.scalatest.FunSuite
import core.parser.ScalaParser._
import core.parser._

class ParserSuite extends FunSuite {
  test("parser is LL1") {
    assert(expr.isLL1)
  }
}
