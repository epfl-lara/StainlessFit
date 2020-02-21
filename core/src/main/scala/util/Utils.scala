package stainlessfit
package core
package util

import trees._

object Utils {
  def mapFirst[A](l: Seq[A], f: A => Option[A]): Option[Seq[A]] = {
    if (l.isEmpty) None
    else
      f(l.head).map(a => a +: l.tail) orElse
      mapFirst(l.tail, f).map(as => l.head +: as)
  }

  def mapFirst2[A](l: List[A], f: A => Option[A]): Option[List[A]] = l match {
    case Nil => None
    case x :: xs =>
      f(x).map(y => y :: xs) orElse
      mapFirst2(xs, f).map(ys => x :: ys)
  }

  def collectFirst[A,B](l: List[A], f: A => Option[B]): Option[B] = l match {
    case Nil => None
    case x ::  xs => f(x) orElse collectFirst(xs, f)
  }

  def mapFirstWithResult[A,B](l: List[A], f: A => Option[(A,B)]): Option[(List[A], B)] = l match {
    case Nil => None
    case x ::  xs =>
      f(x).map[(List[A], B)] { case (y,b) => (y ::  xs, b) } orElse
      mapFirstWithResult(xs, f).map[(List[A], B)]{ case (ys,b) => (x ::  ys, b) }
  }
}
