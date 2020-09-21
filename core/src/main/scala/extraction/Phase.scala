/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package extraction

import core.trees.Tree
import util.RunContext
import trees.Printer
import parser.FitParser

trait Phase[X] { self =>

  implicit val rc: RunContext

  def transform(t: Tree): (Tree, X)

  def andThen[Y](other: Phase[Y]): Phase[(X,Y)] = new Phase[(X,Y)] {
    implicit val rc: RunContext = self.rc

    def transform(t: Tree): (Tree, (X,Y)) = {
      val (t1, x) = self.transform(t)
      val (t2, y) = other.transform(t1)
      (t2, (x, y))
    }
  }
}

trait DebugPhase[X] extends Phase[X] { self =>

  val underlying: Phase[X]

  val name: String
  def transform(t: Tree): (Tree, X) = {
    val debug = rc.debugEnabled(DebugSection.Phases) || rc.debugEnabled(DebugSection(name))
    if (debug) {
      rc.reporter.debug("=" * 100)
      rc.reporter.debug(s"Program before phase $name:\n")
      Printer.exprDebug(t)
      rc.reporter.debug("\n\n\n")
    }

    val (res, x) = underlying.transform(t)

    if (debug) {
      if (res == t)
        rc.reporter.debug(s"Program after phase $name has not changed.")
      else {
        rc.reporter.debug("=" * 100)
        rc.reporter.debug(s"Program after phase $name:\n")
        Printer.exprDebug(res)
        if (x != ())
          rc.reporter.debug(s"\nOutput after phase $name: $x")
        rc.reporter.debug("\n\n\n")
      }
    }

    (res, x)
  }
}

object DebugPhase {
  def apply[X](phase: Phase[X], s: String)(implicit rc0: RunContext): DebugPhase[X] = {
    new DebugPhase[X] {
      val name = s
      val underlying = phase
      implicit val rc = rc0
    }
  }
}
