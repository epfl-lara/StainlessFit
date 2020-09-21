/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core

class EvalFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/eval", _.endsWith("sf"))) {
    test(s"Running file $f") {
      assert(Core.evalFile(new java.io.File(f)).isRight)
    }
  }
}
