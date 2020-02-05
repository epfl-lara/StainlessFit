import Utils._
import org.scalatest.FunSuite

import core.Core

class TypeCheckingFileSuite extends FunSuite {

  val rc = core.util.RunContext.testContext

  for (f <- files("examples/typechecker", _.endsWith("sf"))) {
    test(s"Type checking file $f") {
      val result = Core.typeCheckFile(rc, f, false)
      assert(result.isRight)
      val Right((success, _)) = result
      assert(success)
    }
  }
}
