/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import trees._
import fit.core.util.RunContext

object SDepSugar {

  object BaseType {
    def unapply(ty: Tree): Boolean =
      ty match {
        case TopType | BoolType | NatType | `UnitType` | `LList` => true
        case _ => false
      }
  }

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

  object LNil {
    def apply(): Tree = LeftTree(UnitLiteral)

    def unapply(t: Tree): Boolean =
      t match {
        case LeftTree(UnitLiteral) => true
        case _ => false
      }
  }

  val idHead = Identifier.fresh("x")
  val idTail = Identifier.fresh("xs")
  object LCons {
    // def apply(): Tree =
    //   Lambda(Some(TopType), Bind(idHead,
    //     Lambda(Some(LList), Bind(idTail,
    //       RightTree(Pair(Var(idHead), Var(idTail)))
    //   ))))

    def apply(x: Tree, xs: Tree): Tree = RightTree(Pair(x, xs))

    def unapply(t: Tree): Option[(Tree, Tree)] =
      t match {
        case RightTree(Pair(tHead, tTail)) => Some((tHead, tTail))
        case _ => None
      }
  }

  val nList = Identifier.fresh("n")
  val alpha = Identifier.fresh("alpha")
  val unused = Identifier.fresh("h")
  val LList = Node("List", Nil)

  val LNilType: Tree = SingletonType(LList, LNil())

  val idHead2 = Identifier.fresh("x")
  val idTail2 = Identifier.fresh("xs")

  object LConsType {
    def apply(tyHead: Tree, tyTail: Tree): Tree =
      Node("ConsType", List(tyHead, tyTail))

    def unapply(ty: Tree): Option[(Tree, Tree)] = ty match {
      case Node("ConsType", List(tyHead, tyTail)) =>
        Some((tyHead, tyTail))
      case _ =>
        None
    }
  }


  object ListMatch {
    def apply(l: Tree, tNil: Tree, tCons: Tree): Tree =
      Node("ListMatch", List(l, tNil, tCons))

    def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
      case Node("ListMatch", List(l, tNil, tCons)) =>
        Some((l, tNil, tCons))
      case _ =>
        None
    }

    def lower(l: Tree, tNil: Tree, tCons: Tree): Tree = {
      val Bind(idHead, Bind(idTail, e)) = tCons
      val unused = Identifier.fresh("u")
      val pair = Identifier.fresh("p")
      EitherMatch(l,
        Bind(unused, tNil),
        Bind(pair,
          App(App(
            Lambda(None, Bind(idHead, Lambda(None, Bind(idTail, e )))),
            First(Var(pair))),
            Second(Var(pair))
          )
        )
      )
    }
  }

  object ListMatchType {
    def apply(l: Tree, tyNil: Tree, tyCons: Tree)(implicit rc: RunContext): Tree = tyCons match {
      case Bind(idHead, Bind(idTail, _)) =>
        Node("ListMatchType", List(l, tyNil, tyCons))
      case _ =>
        rc.reporter.fatalError("Expecting two binds in the third argument of `ListMatchType`")
    }

    def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
      case Node("ListMatchType", List(t, tyNil, tyCons)) => Some((t, tyNil, tyCons))
      case _ => None
    }
  }

  object NatMatchType {
    def apply(l: Tree, tyZero: Tree, tySucc: Tree)(implicit rc: RunContext): Tree = tySucc match {
      case Bind(id, _) =>
        Node("NatMatchType", List(l, tyZero, tySucc))
      case _ =>
        rc.reporter.fatalError("Expecting one bind in the third argument of `NatMatchType`")
    }

    def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
      case Node("NatMatchType", List(t, tyZero, tySucc)) => Some((t, tyZero, tySucc))
      case _ => None
    }
  }

  object Choose {
    val unusedPath = Identifier.fresh("p")
    val PathType = LList

    def apply(ty: Tree)(implicit rc: RunContext): Tree = Node("Choose", List(ty))

    def unapply(t: Tree): Option[Tree] = t match {
      case Node("Choose", List(ty)) => Some(ty)
      case _ => None
    }
  }

  object ChooseWithPath {
    def apply(ty: Tree, t: Tree) = Node("Choose", List(ty, t))

    def unapply(t: Tree): Option[(Tree, Tree)] = t match {
      case Node("Choose", List(ty, t)) => Some((ty, t))
      case _ => None
    }
  }

  object FixWithDefault {
    val maxRecDepth = 123

    def apply(ty: Tree, t: Bind, td: Tree, depthFuel: Int): Tree =
      Node("FixWithDefault", List(ty, t, td, NatLiteral(depthFuel)))
    def unapply(t: Tree): Option[(Tree, Bind, Tree, Int)] = t match {
      case Node("FixWithDefault", List(ty, t: Bind, td, NatLiteral(depthFuel))) =>
        Some((ty, t, td, depthFuel.toInt))
      case _ =>
        None
    }

    def lower(t: Bind, td: Tree, depthFuel: Int)(implicit rc: RunContext): Tree = {
      val Bind(fIn, tBody) = t
      val fOut = Identifier.fresh("fOut")
      val fIn2 = Identifier.fresh("fIn2")
      val unused = Identifier.fresh("unused")
      val fuel = Identifier.fresh("fuel")
      val newFuel = Identifier.fresh("newFuel")
      val body = Lambda(Some(NatType), Bind(fuel,
        NatMatch(
          Var(fuel),
          td,
          Bind(newFuel,
            tBody.replace(fIn, App(Var(fIn2), Var(newFuel)))))))
      val fix = Fix(None, Bind(unused, Bind(fIn2, body)))
      LetIn(None, fix, Bind(fOut, App(Var(fOut), NatLiteral(depthFuel))))
    }
  }
}
