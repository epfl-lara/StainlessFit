package cli

import core.Bench.bench

object Main {
  def main(args: Array[String]): Unit = {
    bench.start()
    Config.parse(args).foreach(App.launch)
    bench.stop()
    bench.report()
  }
}
