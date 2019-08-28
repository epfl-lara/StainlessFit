package parser

import verified.trees._

object Util {
  def mapFirst[A](l: Seq[A], f: A => Option[A]): Option[Seq[A]] = {
    if (l.isEmpty) None
    else
      f(l.head).map(a => a +: l.tail) orElse
      mapFirst(l.tail, f).map(as => l.head +: as)
  }

  val freshIdentifier = {
    var n: Int = 0
    (s: String) => {
      n = n + 1
      Identifier(n, s)
    }
  }
}
