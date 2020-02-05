package core
package util

class RunContext(val config: Config) {
  val reporter = new Reporter(config.colors)
  val bench = new Bench()
  bench.start()
}

object RunContext {
  def testContext = new RunContext(Config.default)
}
