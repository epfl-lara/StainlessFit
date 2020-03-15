package stainlessfit
package core
package codegen.utils

object Identifier {
  private val counter = new codegen.utils.UniqueCounter[String]

  def fresh(name: String): Identifier = new Identifier(name)

  def fresh(): Identifier = new Identifier("")
}

class Identifier protected(val name: String) {
  private lazy val id = Identifier.counter.next(name)

  def fullName = s"${name}$id"

  override def toString: String = name
}
