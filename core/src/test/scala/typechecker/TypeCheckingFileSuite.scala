/* Copyright 2019-2020 EPFL, Lausanne */

package fit

import Utils._
import org.scalatest.funsuite.AnyFunSuite
    import scala.sys.process._

import core.Core

class TypeCheckingFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/typechecker", _.endsWith("sf")).sorted) {
    test(s"Type checking file $f") {
      Core.typeCheckFile(new java.io.File(f)) match {
        case Left(err) => rc.reporter.error(err)
        case Right((success, _)) => assert(success)
      }
    }
  }
}


class TypeCheckingCoqValidationFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testCoqContext

  for (f <- files("examples/typechecker", _.endsWith("sf")).sorted) {
    test(s"Type checking file $f") {
      Core.typeCheckFile(new java.io.File(f)) match {
        case Left(err) => rc.reporter.error(err)
        case Right((success, _)) => assert(success)
      }
    }
    test(s"Validating Coq derivation of $f") {
      val cmd = s"coqc ${f.replaceAll("\\.sf*$", ".v")} -Q systemFR SystemFR"
      var output = s"\nCoq command `$cmd`\n Output : "
      val code = cmd ! ProcessLogger(s => {output += s + "\n"})
      assert(code === 0, output)
    }
  }
}
