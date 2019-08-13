import stainless.lang._
import Utils._
import org.scalatest.FunSuite


class TypeCheckingFileSuite extends FunSuite {
  for (f <- files("examples/typechecker", _.endsWith("sc"))) {
    test(s"Type checking file $f") {
      val result = Main.typeCheckFile(f)
      assert(result.isRight)
      val Right((success, _)) = result
      assert(success)
    }
  }
}
