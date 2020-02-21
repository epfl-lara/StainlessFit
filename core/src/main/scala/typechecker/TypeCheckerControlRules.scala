package stainlessfit
package core
package typechecker

import core.trees._

import util.RunContext
import util.Utils._

import Derivation._

trait TypeCheckerControlRules {

  implicit val rc: RunContext

  val FailRule = Rule("FailRule", {
    g => Some((List(), _ =>
      emitErrorWithJudgment("FailRule", g, Some("Goal is not handled"))
    ))
  })

  val CatchErrorGoal = Rule("CatchErrorGoal", {
    case g @ ErrorGoal(c, s) =>
      Some((List(), _ => {
        emitErrorWithJudgment("CatchErrorGoal", g, s)
      }))
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
