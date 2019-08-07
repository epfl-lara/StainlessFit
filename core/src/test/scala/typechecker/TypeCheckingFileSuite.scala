import Utils._
import org.scalatest.FunSuite


class TypeCheckingFileSuite extends FunSuite {
  for (f <- files("examples/typechecker", _.endsWith("sc"))) {
    test(s"Type checking file $f") {
      val (success, _) = Main.typeCheckFile(f)
      assert(success)
    }
  }
}
