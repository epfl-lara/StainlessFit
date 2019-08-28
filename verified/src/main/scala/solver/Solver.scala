package verified
package solver

import z3.scala._

import stainless.annotation._

@ignore
class Solver extends inox.utils.Interruptible {

  private[this] val reporter = new inox.PlainTextReporter(Set.empty)
  private[this] val interruptManager = new inox.utils.InterruptManager(reporter)
  interruptManager.registerForInterrupts(this)

  @volatile
  private[this] var interrupted = false
  private[this] var freed = false

  private[this] var z3 = new Z3Context(
    "MODEL"             -> true,
    "TYPE_CHECK"        -> true,
    "WELL_SORTED_CHECK" -> true
  )

  def getContext: Z3Context = z3

  def free(): Unit = synchronized {
    freed = true
    if (z3 ne null) {
      z3.delete()
      z3 = null
    }
    interruptManager.unregisterForInterrupts(this)
  }

  override def interrupt(): Unit = synchronized {
    if ((z3 ne null) && !interrupted) {
      interrupted = true
      z3.interrupt()
    }
  }

  override def finalize() {
    if (!freed) {
      reporter.error(s"!! Solver ${this.getClass.getName}[${this.hashCode}] not freed properly prior to GC.")
      free()
    }
  }
}

object Solver {
  @extern def getFactory(): Solver = new Solver
  @extern def reclaim(solver: Solver): Unit = solver.free()
}
