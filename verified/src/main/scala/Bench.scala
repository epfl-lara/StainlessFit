package verified

import stainless.annotation._

@extern
class Bench() {

  @ignore
  var startTime = 0L
  @ignore
  var stopTime = 0L

  def start() = {
    startTime = System.nanoTime()
  }

  def stop() = {
    stopTime = System.nanoTime()
  }

  @ignore
  var times: Map[String, Double] = Map()
  @ignore
  var minTimes: Map[String, Double] = Map()
  @ignore
  var maxTimes: Map[String, Double] = Map()
  @ignore
  var counts: Map[String, Int] = Map()

  def time[R](s: String)(block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    minTimes = minTimes.updated(s, Math.min(minTimes.getOrElse(s,Double.MaxValue),t1 - t0))
    maxTimes = maxTimes.updated(s, Math.max(maxTimes.getOrElse(s,0.0),t1 - t0))
    times = times.updated(s, times.getOrElse(s,0.0) + t1 - t0)
    counts = counts.updated(s, counts.getOrElse(s, 0) + 1)
    result
  }

  def report() = {
    val maxSize = times.map(_._1.size).max
    println("====== REPORT ======")
    println(times.map { case (s:String,t:Double) => "== %s: %.2fs\t%.2fs\t%.2fs\t%s".
      format(
        s.padTo(maxSize,' '),
        t/1000000000.0,
        minTimes(s)/1000000000.0,
        maxTimes(s)/1000000000.0,
        counts(s)
      )
    }.toList.sorted.map(s => (1 to s.count(_=='/')).map("  ").mkString + s).mkString("\n"))
    println("Total time: " + (stopTime - startTime)/1000000000.0)
    println("====================")
  }
}

object Bench {
  val bench = new Bench()
}
