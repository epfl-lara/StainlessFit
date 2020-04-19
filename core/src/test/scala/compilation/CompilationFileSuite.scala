package stainlessfit

import Utils._
import org.scalatest.FunSuite
import core.trees._

import core.Core

class CompilationFileSuite extends FunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/compilation", _.endsWith("sf"))) {
    test(s"Running file $f") {
      val compilation = Core.compileFile(f)
      val eval = Core.evalFile(f)

      (Core.evalFile(f), Core.compileFile(f)) match {
        case (Left(_), _) => assert(false)
        case (_, Left(_)) => assert(false)
        case (Right(evalRes), Right(compileRes)) =>
          assert(Printer.exprAsString(evalRes) == compileRes)
      }
    }
  }
}
