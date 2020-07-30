package stainlessfit
package core
package extraction

import util.RunContext
import parser.FitParser
import trees._

import typechecker.SDepSugar._

class BuiltInIdentifiers(implicit val rc: RunContext) extends Phase[Unit] {

  def transform(t: Tree): (Tree, Unit) = {
    (t.preMap(subTree => subTree match {
      case App(Var(Identifier(0, "size")), e)   => Some(Size(e))
      case App(Var(Identifier(0, "left")), e)   => Some(LeftTree(e))
      case App(Var(Identifier(0, "right")), e)  => Some(RightTree(e))
      case App(Var(Identifier(0, "first")), e)  => Some(First(e))
      case App(Var(Identifier(0, "second")), e) => Some(Second(e))
      case App(App(Var(Identifier(0, "cons")), e1), e2) => Some(LCons(e1, e2))
      case TypeApp(Var(Identifier(0, "choose")), ty) => Some(Choose(ty))
      case Var(Identifier(0, "nil"))            => Some(LNil())
      case Var(Identifier(0, "List"))           => Some(LList)
      case _ => None
    }), ())
  }
}

object BuiltInIdentifiers {
  val builtInIdentifiers = Seq(
    "size", "left", "right", "first", "second", "nil", "cons", "choose"
  )

  val builtInTypeIdentifiers = Seq(
    "List"
  )
}
