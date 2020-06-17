package stainlessfit
package core
package typechecker

import trees._
import util.RunContext

object Derivation {

  sealed abstract class Judgment {
    val context: Context
    val name: String
  }

  case class CheckJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment
  case class SubtypeJudgment(override val name: String, override val context: Context, ty1: Tree, ty2: Tree) extends Judgment
  case class InferJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment
  case class AreEqualJudgment(override val name: String, override val context: Context, t1: Tree, t2: Tree, s: String) extends Judgment
  case class ErrorJudgment(override val name: String, goal: Goal, err: Option[String]) extends Judgment {
     override val context: Context = goal.c
  }
  case class SynthesisJudgment(override val name: String, override val context: Context, tp: Tree, t: Tree) extends Judgment
  case class EmptyJudgment(override val name: String, override val context: Context) extends Judgment
  case class FileJudgment(override val name: String, override val context: Context, s: String) extends Judgment

  case class NodeTree[T](node: T, children: List[NodeTree[T]])

  def emitErrorWithJudgment(name: String, goal: Goal, errOpt: Option[String])(implicit rc: RunContext): (Boolean, Judgment) = {
    for (err <- errOpt)
      rc.reporter.error(
        s"""Error while applying rule $name at position ${goal.c.pos}
          |on goal: ${Printer.asString(goal)}
          |$err\n""".stripMargin
      )
    (false, ErrorJudgment(name, goal, errOpt))
  }

}
