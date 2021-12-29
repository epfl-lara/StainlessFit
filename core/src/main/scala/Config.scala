/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core

import java.io.File

sealed abstract class Mode
object Mode {
  case object Eval      extends Mode
  case object PartEval      extends Mode
  case object TypeCheck extends Mode
  case object SDep      extends Mode
  case object Compile   extends Mode
  case object Execute   extends Mode
}

case class Config(
  mode: Mode                       = null,
  file: File                       = null,
  watch: Boolean                   = false,
  html: Boolean                    = false,
  refresh: Int                     = 0,
  bench: Boolean                   = false,
  colors: Boolean                  = true,
  verbose: Boolean                 = false,
  info: Boolean                    = true,
  printUniqueIds: Boolean          = false,
  printUnderlying: Boolean         = false,
  debugSections: Set[DebugSection] = Set.empty,
  llvmPassName: String             = "O1",
)

object Config {
  def default = Config()
}
