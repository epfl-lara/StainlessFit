package stainlessfit
package core

import util.RunContext
import parser.FitParser
import codegen.CodeGen

package object extraction {
  def typecheckerPipeline(implicit rc: RunContext) =
    DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
    DebugPhase(new FixIndexing(), "FixIndexing") andThen
    DebugPhase(new Namer(), "Namer") andThen
    DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers")

  def evalPipeline(implicit rc: RunContext) =
    DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
    DebugPhase(new Namer(), "Namer") andThen
    DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
    DebugPhase(new Erasure(), "Erasure")

  def compilePipeline(implicit rc: RunContext) =
    DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
    DebugPhase(new Namer(), "Namer") andThen  //=> nom unique
    DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
    DebugPhase(new Erasure(), "Erasure") //erasure => LetIn are transformed into lambdas
}
