package stainlessfit
package core
package typechecker

import trees._
import stainlessfit.core.util.RunContext

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
    def apply(): Tree =
      Lambda(Some(TopType), Bind(idHead,
        Lambda(Some(LList), Bind(idTail,
          RightTree(Pair(Var(idHead), Var(idTail)))
      ))))

    def unapply(t: Tree): Option[(Tree, Tree)] =
      t match {
        case RightTree(Pair(tHead, tTail)) => Some((tHead, tTail))
        case _ => None
      }
  }

  val nList = Identifier.fresh("n")
  val alpha = Identifier.fresh("alpha")
  val unused = Identifier.fresh("h")
  val LList = Node("List", Seq())

  val LNilType: Tree = SingletonType(LList, LNil())

  val idHead2 = Identifier.fresh("x")
  val idTail2 = Identifier.fresh("xs")
  // cons :  (head: Top) => (tail: List) => { [List] cons head tail }
  val LConsType: Tree = PiType(TopType, Bind(idHead2,
    PiType(LList, Bind(idTail2,
      SingletonType(LList, App(App(LCons(), Var(idHead2)), Var(idTail2)))
    ))
  ))


  object ListMatch {

    def apply(l: Tree, eNil: Tree, eCons: Tree): Tree = {
      val Bind(idHead, Bind(idTail, e)) = eCons
      val unused = Identifier.fresh("u")
      val pair = Identifier.fresh("p")
      EitherMatch(l,
        Bind(unused, eNil),
        Bind(pair,
          // let idHead = fst pair
          // let idTail = snd pair
          // e
          App(App(
            Lambda(None, Bind(idHead, Lambda(None, Bind(idTail, e )))),
            First(Var(pair))),
            Second(Var(pair))
          )
        )
      )
    }

    def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
      case
        EitherMatch(l,
          Bind(unused, eNil),
          Bind(pair,
            App(App(
              Lambda(None, Bind(idHead, Lambda(None, Bind(idTail, e )))),
              First(Var(pair1))),
              Second(Var(pair2))
            )
          )
        ) if pair1 == pair && pair2 == pair=>
        Some((l, eNil, Bind(idHead, Bind(idTail, e))))
      case _ => None
    }
  }

  object ListMatchType {
    def apply(l: Tree, tyNil: Tree, tyCons: Tree)(implicit rc: RunContext): Tree = tyCons match {
      case Bind(idHead, Bind(idTail, _)) =>
        Node("ListMatchType", Seq(l, tyNil, tyCons))
      case _ =>
        rc.reporter.fatalError("Expecting two binds in the third argument of `ListMatchType`")
    }

    def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
      case Node("ListMatchType", Seq(t, tyNil, tyCons)) => Some((t, tyNil, tyCons))
      case _ => None
    }
  }

  object FixWithDefault {
    val globalFuel = NatLiteral(123)

    def apply(ty: Tree, t: Bind, td: Tree): Tree =
      Node("FixWithDefault", Seq(ty, t, td))
    def unapply(t: Tree): Option[(Tree, Bind, Tree)] = t match {
      case Node("FixWithDefault", Seq(ty, t: Bind, td)) =>
        Some((ty, t, td))
      case _ =>
        None
    }

    def lower(t: Bind, td: Tree)(implicit rc: RunContext): Tree = {
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
      LetIn(None, fix, Bind(fOut, App(Var(fOut), globalFuel)))
    }
  }
}
