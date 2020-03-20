package stainlessfit
package core
package typechecker

import trees._

object ScalaDepSugar {

  object SingletonType {
    def apply(ty: Tree, t: Tree): Tree = {
      val id = Identifier.fresh("x")
      RefinementByType(ty, Bind(id,
        EqualityType(Var(id), t)
      ))
    }

    def unapply(t: Tree): Option[(Tree, Tree)] = t match {
      case RefinementByType(ty, Bind(id, EqualityType(Var(id2), t))) if id == id2 =>
        Some((ty, t))
      case _ =>
        None
    }
  }
}
