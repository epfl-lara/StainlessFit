/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package util

class RunContext(val config: Config) {
  val reporter = new Reporter(config.colors, config.info)
  val bench = new Bench()
  val parser = new core.parser.FitParser()(this)
  val exprPrinter = parser.PrettyPrinter(parser.expr)
  val typePrinter = parser.PrettyPrinter(parser.typeExpr)
  bench.start()

  def debugEnabled(ds: DebugSection): Boolean =
    config.debugSections.contains(ds)
}

object RunContext {
  def testContext = new RunContext(Config.default)
}
