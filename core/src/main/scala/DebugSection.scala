/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core

case class DebugSection(name: String) extends AnyVal {
  override def toString: String = name
}

object DebugSection {
  val Rule                   = DebugSection("rule")
  val TypeCheck              = DebugSection("typecheck")
  val Equality               = DebugSection("equality")
  val Phases                 = DebugSection("phases")
  val DefFunctionElimination = DebugSection("DefFunctionElimination")
  val FixIndexing            = DebugSection("FixIndexing")
  val Namer                  = DebugSection("Namer")
  val BuiltInIdentifiers     = DebugSection("BuiltInIdentifiers")
  val Erasure                = DebugSection("Erasure")

  val available: Set[DebugSection] =
    Set(
      Rule, TypeCheck, Equality, Phases,
      DefFunctionElimination, FixIndexing, Namer, BuiltInIdentifiers,
      Erasure
    )
}
