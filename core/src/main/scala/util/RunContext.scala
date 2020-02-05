package stainlessfit
package core
package util

class RunContext(val config: Config) {
  val reporter = new Reporter(config.colors)
  val bench = new Bench()
  bench.start()

  def debugEnabled(ds: DebugSection): Boolean =
    config.debugSections.contains(ds)
}

object RunContext {
  def testContext = new RunContext(Config.default)
}
