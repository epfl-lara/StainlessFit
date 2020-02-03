package core
package typechecker

import core.trees._

import Derivation._
import util.Utils._
import util.HTMLOutput._

object TypeCheckerUnsoundRules {

  val UnsoundIgnoreEquality = Rule("UnsoundIgnoreEquality", {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug("In context:\n" + c.toString)
      TypeChecker.equalityDebug("Ignoring equality: " + g.toString)
      Some(List(), _ => (true, AreEqualJudgment("UnsoundIgnoreEquality", c, t1, t2, bold("IGNORED"))))
    case g =>
      None
  })

}
