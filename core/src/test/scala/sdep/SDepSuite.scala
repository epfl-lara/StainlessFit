package stainlessfit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core

class SDepSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/sdep", _.endsWith("sf"))) {
    test(s"Type checking file $f") {
      val result = Core.sDepFile(new java.io.File(f))
      assert(result.isRight)
      val Right((success, _)) = result
      assert(success)
    }
  }
}
