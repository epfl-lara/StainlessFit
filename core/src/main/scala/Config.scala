package stainlessfit
package core

import java.io.File

sealed abstract class Mode
object Mode {
  case object Eval      extends Mode
  case object TypeCheck extends Mode
  case object ScalaDep  extends Mode
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
)

object Config {
  def default = Config()
}
