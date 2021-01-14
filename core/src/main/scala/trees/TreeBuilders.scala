/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package trees

object TreeBuilders {
  object Binds {
    def apply(ids: List[Identifier], t: Tree): Tree = {
      ids.foldRight(t)((id, acc) => Bind(id, acc))
    }

    def unapply(t: Tree): Option[(List[Identifier], Tree)] = t match {
      case Bind(id, t2) =>
        val (l, t3) = unapply(t2).get
        Some((id +: l, t3))
      case _ => Some((List(), t))
    }

    def remove(t: Tree): Tree = unapply(t).get._2
  }

  object Sigmas {
    def apply(tys: List[Tree]): Tree = {
      val h = tys.last
      val r = tys.init
      r.foldRight(h) { case (e, acc) =>
        SigmaType(e, Bind(Identifier.fresh("x"), acc)).setPos(e, acc)
      }
    }

    def unapply(ty: Tree): Option[List[Tree]] = ty match {
      case SigmaType(ty1, Bind(id, ty2)) if !id.isFreeIn(ty2) => unapply(ty2).map(ty1 +: _)
      case _ => Some(List(ty))
    }
  }

  object Pairs {
    def apply(ts: List[Tree]): Tree = {
      if (ts.isEmpty) UnitLiteral
      else {
        val h = ts.last
        val r = ts.init
        r.foldRight(h) { case (e, acc) => Pair(e, acc) }
      }
    }

    def unapply(t: Tree): Option[List[Tree]] = t match {
      case Pair(t1, t2) => unapply(t2).map(t1 +: _)
      case _ => Some(List(t))
    }
  }

  object Applications {
    def apply(fun: Tree, args: List[AppArgument]): Tree = {
      args.foldLeft(fun) {
        case (acc, TypeAppArg(ty))    => TypeApp(acc, ty)
        case (acc, AppArg(t))         => App(acc, t)
        case (acc, ErasableAppArg(t)) => ErasableApp(acc, t)
      }
    }

    def unapply(t: Tree): Option[(Tree, List[AppArgument])] = t match {
      case TypeApp(acc, ty) => unapply(acc).map { case (fun, args) => (fun, args :+ TypeAppArg(ty)) }
      case App(acc, t) => unapply(acc).map { case (fun, args) => (fun, args :+ AppArg(t)) }
      case ErasableApp(acc, t) => unapply(acc).map { case (fun, args) => (fun, args :+ ErasableAppArg(t)) }
      case _ => Some((t, List()))
    }
  }

  object PlaceHolder {
    def apply(): Tree = Node("PlaceHolder", Nil)
    def unapply(t: Tree): Boolean = t == Node("PlaceHolder", Nil)
  }

  object Abstractions {
    def apply(args: List[DefArgument], body: Tree): Tree = {
      args.foldRight(body) {
        case (arg, acc) =>
          arg match {
            case TypeArgument(id)       => Abs(Bind(id, acc))
            case ForallArgument(id, ty) => ErasableLambda(ty, Bind(id, acc))
            case TypedArgument(id, ty)  => Lambda(Some(ty), Bind(id, acc))
            case UntypedArgument(id)    => Lambda(None, Bind(id, acc))
          }
      }
    }

    def unapply(t: Tree): Option[(List[DefArgument], Tree)] = t match {
      case Abs(Bind(id, acc)) => unapply(acc).map { case (args, body) => (TypeArgument(id) +: args, body) }
      case ErasableLambda(ty, Bind(id, acc)) => unapply(acc).map { case (args, body) => (ForallArgument(id, ty) +: args, body) }
      case Lambda(Some(ty), Bind(id, acc)) => unapply(acc).map { case (args, body) => (TypedArgument(id, ty) +: args, body) }
      case Lambda(None, Bind(id, acc)) => unapply(acc).map { case (args, body) => (UntypedArgument(id) +: args, body) }
      case _ => Some(Nil, t)
    }
  }

  object DefFunction {
    def apply(id: Identifier, args: List[DefArgument], optRet: Option[Tree], optMeasure: Option[Tree], body: Tree, rest: Tree) = {
      Node("DefFunction", List(
        Abstractions(args, Node("DefFunctionInner1", List(
          optRet.getOrElse(PlaceHolder()),
          optMeasure.getOrElse(PlaceHolder())
        ))),

        Bind(id, Node("DefFunctionInner2", List(body, rest)))
      ))
    }

    def unapply(t: Tree): Option[(Identifier, List[DefArgument], Option[Tree], Option[Tree], Tree, Tree)] = t match {
      case Node("DefFunction", List(
          Abstractions(args, Node("DefFunctionInner1", List(ret, measure))),
          Bind(id, Node("DefFunctionInner2", List(body, rest)))
        )) =>
        Some((id, args,
          if (ret == PlaceHolder()) None else Some(ret),
          if (measure == PlaceHolder()) None else Some(measure),
          body,
          rest
        ))
      case _ => None
    }
  }

  object ForallQuantifiers {
    def apply(args: List[DefArgument], retType: Tree): Tree = {
      args.foldRight(retType) {
        case (arg, accType) =>
          arg match {
            case TypeArgument(id)       => PolyForallType(Bind(id, accType))
            case ForallArgument(id, ty) => IntersectionType(ty, (Bind(id, accType)))
            case TypedArgument(id, ty)  => PiType(ty, Bind(id, accType))
            case UntypedArgument(id)    =>
              throw new Exception(s"Untyped arguments ($id) are not supported in the `ForallQuantifiers` construction")
          }
      }
    }
  }
}
