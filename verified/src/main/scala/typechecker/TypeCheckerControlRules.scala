package verified
package typechecker

import verified.trees._

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.io.StdOut.println

import Derivation._
import Util._
import Formatting._

object TypeCheckerControlRules {

  val FailRule = Rule("FailRule", {
    g => Some((List(), _ =>
      (false, ErrorJudgment("FailRule", g.c, "No more fuel or goal is not handled:\n" + anyToString(g)))
    ))
  })

  val CatchErrorGoal = Rule("CatchErrorGoal", {
    case ErrorGoal(c, s) =>
      Some(List(), _ => (false, ErrorJudgment("CatchErrorGoal", c, s)))
    case g =>
      None()
  })

  val CatchEmptyGoal = Rule("CatchEmptyGoal", {
    case EmptyGoal(c) =>
      Some(List(), _ => (true, EmptyJudgment("CatchEmptyGoal", c)))
    case g =>
      None()
  })
}
