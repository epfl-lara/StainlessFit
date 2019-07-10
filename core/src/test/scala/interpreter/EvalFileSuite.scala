import Utils._
import org.scalatest.FunSuite

class EvalFileSuite extends FunSuite {

  for (f <- files("examples", _.endsWith("sc"))) {
    test(s"Running file $f") {
      Main.evalFile(f)
    }
  }
}
