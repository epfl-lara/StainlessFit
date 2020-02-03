package core
package typechecker

import core.trees._

object Derivation {

  sealed abstract class Judgment {
    val context: Context
    val name: String
  }

  case class CheckJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment
  case class InferJudgment(override val name: String, override val context: Context, e: Tree, t: Tree) extends Judgment
  case class AreEqualJudgment(override val name: String, override val context: Context, t1: Tree, t2: Tree, s: String) extends Judgment
  case class ErrorJudgment(override val name: String, override val context: Context, error: String) extends Judgment
  case class SynthesisJudgment(override val name: String, override val context: Context, tp: Tree, t: Tree) extends Judgment
  case class EmptyJudgment(override val name: String, override val context: Context) extends Judgment
  case class FileJudgment(override val name: String, override val context: Context, s: String) extends Judgment

  case class NodeTree[T](node: T, children: List[NodeTree[T]])

}
