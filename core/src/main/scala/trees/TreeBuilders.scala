package stainlessfit
package core
package trees

object TreeBuilders {
  object Binds {
    def apply(ids: Seq[Identifier], t: Tree): Tree = {
      ids.foldRight(t)((id, acc) => Bind(id, acc))
    }

    def unapply(t: Tree): Option[(Seq[Identifier], Tree)] = t match {
      case Bind(id, t2) =>
        val (l, t3) = unapply(t2).get
        Some((id +: l, t3))
      case _ => Some((Seq(), t))
    }

    def remove(t: Tree): Tree = unapply(t).get._2
  }

  object Sigmas {
    def apply(tys: Seq[Tree]): Tree = {
      val h = tys.last
      val r = tys.init
      r.foldRight(h) { case (e, acc) =>
        SigmaType(e, Bind(Identifier.fresh("x"), acc)).setPos(e, acc)
      }
    }

    def unapply(ty: Tree): Option[Seq[Tree]] = ty match {
      case SigmaType(ty1, Bind(id, ty2)) if !id.isFreeIn(ty2) => unapply(ty2).map(ty1 +: _)
      case _ => Some(Seq(ty))
    }
  }

  object Pairs {
    def apply(ts: Seq[Tree]): Tree = {
      if (ts.isEmpty) UnitLiteral
      else {
        val h = ts.last
        val r = ts.init
        r.foldRight(h) { case (e, acc) => Pair(e, acc) }
      }
    }

    def unapply(t: Tree): Option[Seq[Tree]] = t match {
      case Pair(t1, t2) => unapply(t2).map(t1 +: _)
      case _ => Some(Seq(t))
    }
  }

  object Applications {
    def apply(fun: Tree, args: Seq[AppArgument]): Tree = {
      args.foldLeft(fun) {
        case (acc, TypeAppArg(ty))    => TypeApp(acc, ty)
        case (acc, AppArg(t))         => App(acc, t)
        case (acc, ErasableAppArg(t)) => ErasableApp(acc, t)
      }
    }

    def unapply(t: Tree): Option[(Tree, Seq[AppArgument])] = t match {
      case TypeApp(acc, ty) => unapply(acc).map { case (fun, args) => (fun, args :+ TypeAppArg(ty)) }
      case App(acc, t) => unapply(acc).map { case (fun, args) => (fun, args :+ AppArg(t)) }
      case ErasableApp(acc, t) => unapply(acc).map { case (fun, args) => (fun, args :+ ErasableAppArg(t)) }
      case _ => Some((t, Seq()))
    }
  }

  object Abstractions {
    def apply(args: Seq[DefArgument], body: Tree): Tree = {
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

    def unapply(t: Tree): Option[(Seq[DefArgument], Tree)] = t match {
      case Abs(Bind(id, acc)) => unapply(acc).map { case (args, body) => (TypeArgument(id) +: args, body) }
      case ErasableLambda(ty, Bind(id, acc)) => unapply(acc).map { case (args, body) => (ForallArgument(id, ty) +: args, body) }
      case Lambda(Some(ty), Bind(id, acc)) => unapply(acc).map { case (args, body) => (TypedArgument(id, ty) +: args, body) }
      case Lambda(None, Bind(id, acc)) => unapply(acc).map { case (args, body) => (UntypedArgument(id) +: args, body) }
      case _ => Some(Seq(), t)
    }
  }

  object ForallQuantifiers {
    def apply(args: Seq[DefArgument], retType: Tree): Tree = {
      args.foldRight(retType) {
        case (arg, accType) =>
          arg match {
            case TypeArgument(id)       => PolyForallType(Bind(id, accType))
            case ForallArgument(id, ty) => IntersectionType(ty, (Bind(id, accType)))
            case TypedArgument(id, ty)  => PiType(ty, Bind(id, accType))
            case UntypedArgument(id)     =>
              throw new Exception(s"Untyped arguments ($id) are not supported in the `ForallQuantifiers` construction")
          }
      }
    }
  }
}
