package stainlessfit

import Utils._
import org.scalatest.funsuite.AnyFunSuite

import core.Core
import stainlessfit.core.partialEvaluator.PartialEvaluator

class PartEvalFileSuite extends AnyFunSuite {

  implicit val rc = core.util.RunContext.testContext

  for (f <- files("examples/eval", _.endsWith("sf"))) {
    test(s"Running file $f") {
      val file = new java.io.File(f)

      val evaled = Core.evalFile(file)
      val partevaled = Core.partEvalFile(file)
      
      assert(evaled === partevaled)
    }
  }
  
  for (f <- files("examples/parteval/expected", _.endsWith("sf"))) {
    val remover = """expected(\\|\/)""".r
    val codeFileName = remover.replaceAllIn(f,"")
    test(s"Running file $f") {
      val expectedResultFile = new java.io.File(f)
      val codeFile = new java.io.File(codeFileName)

      val pe = Core.parseFile(expectedResultFile)
      pe match {
        case Left(value) => 
          assert(false,value)
        case Right(value) =>
          val (expectedResult, _) = PartialEvaluator.pipeline().transform(value)
          val res = Core.partEvalFile(codeFile)
          res match {
            case Left(value) => 
              assert(false, value)
            case Right(result) =>
              assert(result === expectedResult)
          }
      }
    }
  }
  
}
