package stainlessfit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core

class TypeCheckingFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext
  // test.coq = 1

  for (f <- files("examples/typechecker", _.endsWith("sf"))) {
    test(s"Type checking file $f") {
      Core.typeCheckFile(new java.io.File(f)) match {
        case Left(err) => rc.reporter.error(err)
        case Right((success, _)) => assert(success)
      }
    }
    /*
    test(s"Validating Coq derivation of $f") {
      ???
    }*/
  }
}
