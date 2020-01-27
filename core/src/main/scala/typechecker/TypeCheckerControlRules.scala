package core
package typechecker

import core.trees._


import Derivation._
import Util._
import Formatting._

object TypeCheckerControlRules {

  val FailRule = Rule("FailRule", {
    g => Some((List(), _ =>
      (false, ErrorJudgment("FailRule", g.c, "Goal is not handled:\n" + g.toString))
    ))
  })

  val CatchErrorGoal = Rule("CatchErrorGoal", {
    case ErrorGoal(c, s) =>
      Some(List(), _ => (false, ErrorJudgment("CatchErrorGoal", c, s)))
    case g =>
      None
  })

  val CatchEmptyGoal = Rule("CatchEmptyGoal", {
    case EmptyGoal(c) =>
      Some(List(), _ => (true, EmptyJudgment("CatchEmptyGoal", c)))
    case g =>
      None
  })
}
