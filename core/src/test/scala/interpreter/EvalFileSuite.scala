package stainlessfit

import Utils._
import org.scalatest.FunSuite

import core.Core

class EvalFileSuite extends FunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/eval", _.endsWith("sf"))) {
    test(s"Running file $f") {
      assert(Core.evalFile(f).isRight)
    }
  }
}
