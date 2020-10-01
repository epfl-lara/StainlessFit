package stainlessfit
package core
package trees

import util.RunContext
import parser.FitParser

case class Identifier(id: Int, name: String) extends Positioned {
  override def toString: String = name
  def uniqueString: String = name + "#" + id

  def asString(implicit rc: RunContext): String = Printer.asString(this)

  def isTypeIdentifier: Boolean = name.size > 0 && name(0).isUpper
  def isTermIdentifier: Boolean = name.size > 0 && name(0).isLower

  def freshen(): Identifier = Identifier.fresh(name)

  def wrap: String = {
    if (isTypeIdentifier) s"[$this]"
    else s"($this)"
  }

  def isFreeIn(e: Tree): Boolean = {
    e.exists({
      case Bind(x, e) if x == this => false
      case _ => true
    }, {
      case Var(x) => x == this
      case _ => false
    })
  }
}

object Identifier {
  var id = 0

  def fresh(): Int = {
    id = id + 1
    id
  }

  def fresh(name: String): Identifier = {
    Identifier(fresh(), name)
  }
}
