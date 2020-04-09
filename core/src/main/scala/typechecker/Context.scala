package stainlessfit
package core
package typechecker

import trees._
import util.RunContext

object Context {
  def empty(implicit rc: RunContext): Context = Context(Map(), Set(), 0, 0)
  def empty(max: Int)(implicit rc: RunContext): Context = Context(Map(), Set(), 0, max)
}

case class Context(
  val termVariables: Map[Identifier, Tree],
  val typeVariables: Set[Identifier],
  val level: Int,
  val n: Int // All variables in the context must have an identifier strictly smaller than n.
)(implicit rc: RunContext) extends Positioned {

  def bind(i: Identifier, t: Tree): Context = {
    if (termVariables.contains(i)) throw new Exception("Already bound " + i.toString)
    copy(
      termVariables = termVariables.updated(i, t)
    )
  }

  def addTypeVariable(i: Identifier): Context = copy(typeVariables = typeVariables + i)

  def bindFresh(s: String, t: Tree): (Identifier, Context) = (Identifier(n, s), bind(Identifier(n, s), t).copy(n = n+1))

  def getFresh(s: String): (Identifier, Context) = (Identifier(n, s), copy(n = n+1))

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree): Context = bindFresh("eq", EqualityType(t1, t2))._2

  def incrementLevel: Context = copy(level = level + 1)

  def containsVarOfType(tp: Tree): Boolean =
    termVariables.exists(_._2 == tp)

  def getVarOfType(tp: Tree): Option[Identifier] =
    termVariables.find(_._2 == tp).map(_._1)

  override def toString: String = {
    Printer.asString(this)(rc)
  }

  def hasRefinement: Boolean = {
    termVariables.exists { case (v, tp) =>
      tp match {
        case RefinementType(_, _) => true
        case _ => false
      }
    }
  }

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Context = {
    copy(
      termVariables = termVariables.map {
        case (v, tp) => (v, tp.replace(id, t))
      }
    )
  }
}
