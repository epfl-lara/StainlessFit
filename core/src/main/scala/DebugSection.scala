package stainlessfit
package core

case class DebugSection(name: String) extends AnyVal {
  override def toString: String = name
}

object DebugSection {
  val Rule      = DebugSection("rule")
  val TypeCheck = DebugSection("typecheck")
  val Equality  = DebugSection("equality")

  val available: Set[DebugSection] = Set(Rule, TypeCheck, Equality)
}

