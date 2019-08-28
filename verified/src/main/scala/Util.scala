package verified

import stainless.annotation._

object Util {
  @extern def replaceAll(s: String, e1: String, e2: String): String = s.replaceAll(e1, e2)
  @extern def length(s: String): Int = s.length
  @extern def bigIntToInt(i: BigInt): Int = i.toInt
  @extern def throwException[T](s: String): T = throw new java.lang.Exception(s)
  @extern def anyToString[T](t: T): String = t.toString
}
