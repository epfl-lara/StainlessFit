package stainlessfit
package core

import util.RunContext
import parser.FitParser

package object extraction {
  def pipeline(implicit rc: RunContext) =
    DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
    DebugPhase(new FixIndexing(), "FixIndexing") andThen
    DebugPhase(new Namer(), "Namer") andThen
    DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers")
}
