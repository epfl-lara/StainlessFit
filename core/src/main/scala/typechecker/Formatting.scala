package core
package typechecker

import core.Util._
import core.trees._

object Formatting {
  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)
  def headerColor(s: String) = color("#002875", s)
  def bold(s: String) = s"<b>$s</b>"

  def shortString(s: String, maxWidth: Int = 90): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  def termOutput(t: Tree): String =
    termColor(shortString(t.toString))

  def typeOutput(t: Tree): String =
    typeColor(shortString(t.toString))
}
