package stainlessfit

import Utils._
import org.scalatest.FunSuite
import core.trees._

import core.Core

class CompilationFileSuite extends FunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/compilation", _.endsWith("sf"))) {
    test(s"Running file $f") {
      val eval = Core.evalFile(f)
      val execute = Core.executeFile(f, false)

      (eval, execute) match {
        case (Left(a), Left(b)) => assert(a == b)
        case (Right(evalRes), Right(compileRes)) =>
          assert(Printer.exprAsString(evalRes) == compileRes)
        case (_, _) => assert(false)
      }
    }
  }
}
