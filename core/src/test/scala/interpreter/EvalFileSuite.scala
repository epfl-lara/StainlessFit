import Utils._
import org.scalatest.FunSuite

import core.Core

class EvalFileSuite extends FunSuite {

  for (f <- files("examples/eval", _.endsWith("sf"))) {
    test(s"Running file $f") {
      assert(Core.evalFile(f).isRight)
    }
  }
}
