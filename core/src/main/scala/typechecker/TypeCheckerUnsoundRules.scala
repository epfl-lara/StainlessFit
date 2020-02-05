package core
package typechecker

import core.trees._

import util.Utils._
import util.RunContext

import Derivation._

trait TypeCheckerUnsoundRules {

  val rc: RunContext

  val UnsoundIgnoreEquality = Rule("UnsoundIgnoreEquality", {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug(rc, "In context:\n" + c.toString)
      TypeChecker.equalityDebug(rc, "Ignoring equality: " + g.toString)
      Some(List(), _ => (true, AreEqualJudgment("UnsoundIgnoreEquality", c, t1, t2, "<b>IGNORED</b>")))
    case g =>
      None
  })

}
