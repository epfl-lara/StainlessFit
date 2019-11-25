package verified
package typechecker

import stainless.annotation._

import Util._
import verified.trees._

object Formatting {
  @extern def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  @extern def termColor(s: String) = color("#007c46", s)
  @extern def typeColor(s: String) = color("#9b2600", s)
  @extern def headerColor(s: String) = color("#002875", s)
  @extern def bold(s: String) = s"<b>$s</b>"

  @extern def shortString(s: String, maxWidth: Int = 160): String = {
    val r = replaceAll(s, "\n", " ")
    if (length(r) > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  @extern def termOutput(t: Tree): String =
    termColor(shortString(t.toString))

  @extern def typeOutput(t: Tree): String =
    typeColor(shortString(t.toString))
}
