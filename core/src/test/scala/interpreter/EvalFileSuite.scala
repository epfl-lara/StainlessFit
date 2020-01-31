import Utils._
import org.scalatest.FunSuite

import core.Core

class EvalFileSuite extends FunSuite {

  for (f <- files("examples/parser", _.endsWith("sc"))) {
    test(s"Running file $f") {
      assert(Core.evalFile(f).isRight)
    }
  }
}
