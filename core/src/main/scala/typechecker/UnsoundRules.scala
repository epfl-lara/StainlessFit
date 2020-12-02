/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import core.trees._

import util.Utils._
import util.RunContext

import Derivation._

trait UnsoundRules {

  implicit val rc: RunContext

  val UnsoundIgnoreEquality = Rule("UnsoundIgnoreEquality", {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug("In context:\n" + c.toString)
      TypeChecker.equalityDebug("Ignoring equality: " + g.toString)
      Some(List(), _ => (true, AreEqualJudgment("UnsoundIgnoreEquality", c, t1, t2, "<b>IGNORED</b>")))
    case g =>
      None
  })

}
