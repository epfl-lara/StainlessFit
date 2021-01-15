package stainlessfit
package core
package partialEvaluator

import trees._
import util.RunContext
import TreeUtils.replaceSmallStep
import parser.FitParser
import stainlessfit.core.util.Utils

trait Measure {
  //postcondition: res must be lower bounded !
  def apply(t: Tree): BigInt
}

object TreeSize extends Measure {

  override def apply(t: Tree): BigInt = {
    val (children, reconstruct) = t.deconstruct
    1 + children.map(TreeSize(_)).fold(BigInt(0))(_ + _)
  }

}