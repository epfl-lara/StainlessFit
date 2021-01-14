/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import trees._
import util.RunContext
import scala.collection.immutable.SeqMap

object Context {
  def empty(implicit rc: RunContext): Context = Context(SeqMap(), Seq(), 0)
  def empty(max: Int)(implicit rc: RunContext): Context = Context(SeqMap(), Seq(), 0)
}

sealed abstract class ContextModifier
case object Same extends ContextModifier
case class Append(addedElements: List[(Identifier, Tree)]) extends ContextModifier
case class New(context: Context) extends ContextModifier
/* To be extended */


case class Context(
  val termVariables: SeqMap[Identifier, Tree],
  val typeVariables: Seq[Identifier],
  val level: Int,
  val lastOp: ContextModifier = Same
)(implicit rc: RunContext) extends Positioned {

  def bind(i: Identifier, ty: Tree): Context = {
    if (termVariables.contains(i)) throw new Exception("Already bound " + i.toString)
    copy(
      termVariables = termVariables.updated(i, ty),
      lastOp = lastOp match {
        case Append(addedElements) => Append((i,ty) +: addedElements)
        case _ => Append(List((i, ty)))
      }
    )
  }

  def addTypeVariable(i: Identifier): Context = 
    copy(typeVariables = typeVariables :+ i )

  def bindFresh(s: String, t: Tree): (Identifier, Context) = {
    val freshId = Identifier.fresh(s)
    (freshId, bind(freshId, t))
  }

  def setModifier(m: ContextModifier) : Context = copy(lastOp = m)

  def contains(id: Identifier): Boolean = termVariables.contains(id)

  def getTypeOf(id: Identifier): Option[Tree] = termVariables.get(id)

  def addEquality(t1: Tree, t2: Tree): Context = {
    bindFresh("eq", EqualityType(t1, t2))._2
  }

  def incrementLevel: Context = copy(level = level + 1, lastOp = Same)

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

  def freshen(t: Tree)(implicit rc: RunContext): Tree = {
    var newIds = Map.empty[Identifier, Identifier]
    def visit(t: Tree): Option[Tree] = t match {
      case Bind(id, t) if this.termVariables.contains(id) =>
        val idN = id.freshen()
        newIds += id -> idN
        Some(Bind(idN, t.replace(id, idN)))
      case _ =>
        None
    }
    t.preMap(visit)
  }

  def bindAndFreshen(id: Identifier, ty: Tree, t: Tree)(implicit rc: RunContext): (Context, Tree) = {
    val c = this.bind(id, ty)
    (c, c.freshen(t))
  }
}
