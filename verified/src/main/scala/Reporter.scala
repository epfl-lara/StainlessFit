package verified

import stainless.annotation._

@ignore
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
    error(e.getStackTrace.mkString("\n"))
  }

  def error(s: String): Unit = {
    println(addPrefix(s, color("[ERROR] ", Console.RED)))
  }

  def warning(s: String): Unit = {
    println(addPrefix(s, color("[WARNING] ", Console.YELLOW)))
  }

  def info(s: String): Unit = {
    println(addPrefix(s, color("[INFO] ", Console.BLUE)))
  }
}
