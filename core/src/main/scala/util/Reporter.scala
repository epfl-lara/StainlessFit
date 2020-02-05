package core
package util

import trees.Position

class Reporter(colors: Boolean) {

  def addPrefix(s: String, pre: String): String = {
    pre + s.replaceAll("\n", "\n" + pre)
  }

  def color(s: String, color: String): String = {
    if (colors)
      color + s + Console.RESET
    else
      s
  }

  def error(e: Throwable): Unit = {
    error(e.toString)
    error(e.getStackTrace.mkString("\n"))
  }

  def error(s: String): Unit = {
    println(addPrefix(s, color("[ERROR] ", Console.RED)))
  }

  def error(p: Position, s: String): Unit = {
    error(s"Error at position $p:")
    error(s)
  }

  def warning(s: String): Unit = {
    println(addPrefix(s, color("[WARNING] ", Console.YELLOW)))
  }

  def info(s: String): Unit = {
    println(addPrefix(s, color("[INFO] ", Console.BLUE)))
  }
}

object Reporter {
  def testReporter = new Reporter(true)
}
