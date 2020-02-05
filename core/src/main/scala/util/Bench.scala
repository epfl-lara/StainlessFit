package core
package util

class Bench() {

  var startTime = 0L
  var stopTime = 0L

  def start() = {
    startTime = System.nanoTime()
  }

  def stop() = {
    stopTime = System.nanoTime()
  }

  var times: Map[String, Double] = Map()
  var minTimes: Map[String, Double] = Map()
  var maxTimes: Map[String, Double] = Map()
  var counts: Map[String, Int] = Map()

  def time[R](s: String)(block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    minTimes = minTimes.updated(s, Math.min(minTimes.getOrElse(s, Double.MaxValue), t1 - t0))
    maxTimes = maxTimes.updated(s, Math.max(maxTimes.getOrElse(s, 0.0), t1 - t0))
    times = times.updated(s, times.getOrElse(s,0.0) + t1 - t0)
    counts = counts.updated(s, counts.getOrElse(s, 0) + 1)
    result
  }

  def seconds(ns: Double): String = s"${(ns / 1000000).toInt}ms"

  def surround(s: String, n: Int, c: Char): String = {
    c.toString * ((n - s.length) / 2) +
    s +
    c.toString * (n - s.length - (n - s.length) / 2)
  }

  case class Table(rows: Seq[Row]) {
    def toString(head: String = ""): String = {
      val ms = rows.map(_.l).transpose.map(c => c.map(_.length).max)
      val width = ms.sum + 2 * (ms.size - 1)
      surround(" REPORT ", width, '=') + "\n" +
      rows.map(_.toString(ms)).mkString("\n")
    }
  }

  case class Row(l: Seq[String]) {
    def maxLength(): Int = l.map(_.length).max

    def toString(ms: Seq[Int]): String = {
      l.zip(ms).map { case (e,m) => e.toString.padTo(m, ' ') }.mkString("  ")
    }
  }


  object Row {
    def apply(e: Any, es: Any*): Row = {
      Row((e +: es).toSeq.map(_.toString))
    }
  }

  def report(reporter: Reporter) = {
    val sizes = times.map(_._1.size)
    val maxSize = if (sizes.isEmpty) 80 else sizes.max
    val t = Table(
      Row(
        "Name",
        "Total",
        // "Min",
        // "Max",
        // "Average",
        "Times"
      ) +:
      times.map { case (name, total) =>
        Seq(
          name,
          total,
          // seconds(minTimes(name)),
          // seconds(maxTimes(name)),
          // seconds(total / counts(name)),
          counts(name).toString
        )
      }.toSeq.sortBy(l => -(l(1).asInstanceOf[Double]))(Ordering.Double.TotalOrdering)
             .map(l => Row(l.updated(1, seconds(l(1).asInstanceOf[Double]))
                            .map(_.toString)))
    )
    reporter.info(t.toString("TIMES"))
    reporter.info("Sum times:  " + seconds(times.values.sum))
    reporter.info("Total time: " + seconds(stopTime - startTime))
  }
}
