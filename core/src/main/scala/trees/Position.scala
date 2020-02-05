package stainlessfit
package core
package trees

import Position._

sealed abstract class Position {
  def widen(other: Position): Position
}

case object NoPosition extends Position {
  override def toString = "?:?"

  def widen(other: Position): Position = other
}

case class DefinedPosition(l1: Int, c1: Int, l2: Int, c2: Int) extends Position {
  override def toString = {
    if (l1 == l2)
      if (c1 == c2) s"$l1:$c1"
      else s"$l1:$c1-$c2"
    else
      s"$l1:$c1-$l2:$c2"
  }

  def widen(other: Position): Position = other match {
    case NoPosition => this
    case DefinedPosition(l3, c3, l4, c4) =>
      val (l5, c5) = smallestLineColum(l1, c1, l3, c3)
      val (l6, c6) = largestLineColum(l2, c2, l4, c4)
      DefinedPosition(l5, c5, l6, c6)
  }
}

trait Positioned {
  var pos: Position = NoPosition

  def setPos(newPos: Position): this.type = {
    pos = newPos
    this
  }

  def setPos(p1: (Int, Int), p2: (Int, Int)): this.type = {
    pos = DefinedPosition(p1._1, p1._2, p2._1, p2._2)
    this
  }

  def setPos(pp: ((Int, Int), (Int, Int))): this.type = {
    pos = DefinedPosition(pp._1._1, pp._1._2, pp._2._1, pp._2._2)
    this
  }

  def setPos(l: Int, c: Int): this.type = {
    pos = DefinedPosition(l, c, l, c)
    this
  }

  def setPos(l1: Int, c1: Int, l2: Int, c2: Int): this.type = {
    pos = DefinedPosition(l2, c2, l2, c2)
    this
  }

  def setPos(others: Positioned*): this.type = {
    pos = others.map(_.pos).fold(pos)((a1, a2) => a1.widen(a2))
    this
  }
}

object Position {
  def apply(l: Int, c: Int): Position = DefinedPosition(l, c, l, c)
  def apply(l1: Int, c1: Int, l2: Int, c2: Int): Position = DefinedPosition(l1, c1, l2, c2)

  def smallerLineColumn(l1: Int, c1: Int, l2: Int, c2: Int): Boolean = {
    l1 < l2 || (l1 == l2 && c1 < c2)
  }

  def smallestLineColum(l1: Int, c1: Int, l2: Int, c2: Int): (Int, Int) = {
    if (smallerLineColumn( l1, c1, l2, c2)) (l1, c1)
    else (l2, c2)
  }

  def largestLineColum(l1: Int, c1: Int, l2: Int, c2: Int): (Int, Int) = {
    if (smallerLineColumn( l1, c1, l2, c2)) (l2, c2)
    else (l1, c1)
  }
}
