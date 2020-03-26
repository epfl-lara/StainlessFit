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

  val LNil: Tree = LeftTree(UnitLiteral)

  val idHead = Identifier.fresh("x")
  val idTail = Identifier.fresh("xs")
  val LCons: Tree = Lambda(None, Bind(idHead, Lambda(None, Bind(idTail,
    RightTree(Pair(Var(idHead), Var(idTail)))
  ))))

  val nList = Identifier.fresh("n")
  val alpha = Identifier.fresh("alpha")
  val unused = Identifier.fresh("h")
  val LList = Node("List", Seq())
  // IntersectionType(NatType, Bind(nList,
  //   RecType(Var(nList), Bind(alpha,
  //     SumType(UnitType, SigmaType(TopType, Bind(unused, Var(alpha))))
  //   ))
  // ))

  val idHead2 = Identifier.fresh("x")
  val idTail2 = Identifier.fresh("xs")
  // cons :  (head: Top) => (tail: List) => { [List] cons head tail }
  val LConsType: Tree = PiType(TopType, Bind(idHead2,
    PiType(LList, Bind(idTail2,
      SingletonType(LList, App(App(LCons, Var(idHead2)), Var(idTail2)))
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

  // object ListMatchType {
  //   def apply(l: Tree, tyNil: Tree, tyCons: Tree): Tree = {
  //     val Bind(idHead, Bind(idTail, ty)) = tyCons
  //     val unused = Identifier.fresh("u")
  //     UnionType(
  //       RefinementByType(tyNil, Bind(unused, EqualityType(l, LNil))),
  //       ExistsType(TopType, Bind(idHead, ExistsType(LList, Bind(idTail,
  //         SigmaType(
  //           EqualityType(l, App(App(LCons, Var(idHead)), Var(idTail))),
  //           Bind(unused, tyCons)
  //         )
  //       ))))
  //     )
  //   }

  //   def unapply(t: Tree): Option[(Tree, Tree, Tree)] = t match {
  //     case
  //       UnionType(
  //         RefinementByType(tyNil, Bind(_, EqualityType(l, LNil))),
  //         ExistsType(TopType, Bind(idHead, ExistsType(LList, Bind(idTail,
  //           SigmaType(
  //             EqualityType(l2, App(App(LCons, Var(idHead2)), Var(idTail2))),
  //             Bind(_, tyCons)
  //           )
  //         ))))
  //       )
  //     if idHead2 == idHead && idTail2 == idTail && l == l2 =>
  //       Some((l, tyNil, Bind(idHead, Bind(idTail, tyCons))))
  //     case _ => None
  //   }
  // }

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
}
