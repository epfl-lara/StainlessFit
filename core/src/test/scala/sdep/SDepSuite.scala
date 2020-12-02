/* Copyright 2019-2020 EPFL, Lausanne */

package fit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core

class SDepSuite extends AnyFunSuite {
  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/sdep", _.endsWith("sf"))) {
    test(s"Type checking file $f") {
      Core.sDepFile(new java.io.File(f)) match {
        case Left(err) => rc.reporter.error(err)
        case Right((success, _)) => assert(success)
      }
    }
  }
}
