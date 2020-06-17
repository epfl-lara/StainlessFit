package stainlessfit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core

class TypeCheckingFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/typechecker", _.endsWith("sf"))) {
    test(s"Type checking file $f") {
      val result = Core.typeCheckFile(new java.io.File(f))
      assert(result.isRight)
      val Right((success, _)) = result
      assert(success)
    }
  }
}
