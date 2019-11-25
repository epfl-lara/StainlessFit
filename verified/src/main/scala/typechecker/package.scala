package verified

package object typechecker {

  import stainless.collection._
  import stainless.lang._

  def collectFirst[A,B](l: List[A], f: A => Option[B]): Option[B] = l match {
    case Nil() => None()
    case Cons(x, xs) => f(x) orElse collectFirst(xs, f)
  }

  def mapFirst[A](l: List[A], f: A => Option[A]): Option[List[A]] = l match {
    case Nil() => None()
    case Cons(x, xs) =>
      f(x).map[List[A]](y => Cons(y, xs)) orElse
      mapFirst(xs, f).map[List[A]](ys => Cons(x, ys))
  }

  def mapFirstWithResult[A,B](l: List[A], f: A => Option[(A,B)]): Option[(List[A], B)] = l match {
    case Nil() => None()
    case Cons(x, xs) =>
      f(x).map[(List[A], B)] { case (y,b) => (Cons(y, xs), b) } orElse
      mapFirstWithResult(xs, f).map[(List[A], B)]{ case (ys,b) => (Cons(x, ys), b) }
  }
}
