package stainlessfit
package core
package extraction

import util.RunContext
import parser.FitParser
import trees._

class BuiltInIdentifiers(implicit val rc: RunContext) extends Phase[Unit] {

  def transform(t: Tree): (Tree, Unit) = {
    (t.replaceMany(subTree => subTree match {
      case App(Var(Identifier(0, "size")), e) => Some(Size(e))
      case App(Var(Identifier(0, "left")), e) => Some(LeftTree(e))
      case App(Var(Identifier(0, "right")), e) => Some(RightTree(e))
      case App(Var(Identifier(0, "first")), e) => Some(First(e))
      case App(Var(Identifier(0, "second")), e) => Some(Second(e))
      case _ => None
    }), ())
  }
}

object BuiltInIdentifiers {
  val builtInIdentifiers = Seq("size", "left", "right", "first", "second")
}
