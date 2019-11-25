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

object TypeCheckerUnsoundRules {

  val UnsoundIgnoreEquality = Rule("UnsoundIgnoreEquality", {
    case g @ EqualityGoal(c, t1, t2) =>
      TypeChecker.equalityDebug("In context:\n" + c.toString)
      TypeChecker.equalityDebug("Ignoring equality: " + anyToString(g))
      Some(List(), _ => (true, AreEqualJudgment("UnsoundIgnoreEquality", c, t1, t2, bold("IGNORED"))))
    case g =>
      None()
  })

}
