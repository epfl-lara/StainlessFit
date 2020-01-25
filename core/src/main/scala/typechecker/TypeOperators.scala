package core
package typechecker

import trees._


object TypeOperators {
  private def unify(t1: Tree, t2: Tree, f: (Tree, Tree) => Tree): Option[Tree] = {
    (t1, t2) match {
      case (UnitType, UnitType) => Some(UnitType)
      case (NatType, NatType) => Some(NatType)
      case (BoolType, BoolType) => Some(BoolType)
      case (TopType, TopType) => Some(TopType)
      case (SumType(t11, t12), SumType(t21, t22)) =>
        unify(t11, t21, f).flatMap { t1 =>
          unify(t12, t22, f).map { t2 =>
            SumType(t1, t2)
          }
        }
      case (PiType(a1, Bind(x, b1)), PiType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            PiType(a, Bind(x, b))
          }
        }
      case (IntersectionType(a1, Bind(x, b1)), IntersectionType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            IntersectionType(a, Bind(x, b))
          }
        }
      case (PolyForallType(Bind(x, b1)), PolyForallType(Bind(x2, b2))) =>
        unify(b1, Tree.replace(x2, Var(x), b2), f).map(b =>
          PolyForallType(Bind(x, b))
        )
      case (SigmaType(a1, Bind(x, b1)), SigmaType(a2, Bind(x2, b2))) =>
        unify(a1, a2, f).flatMap { a =>
          unify(b1, Tree.replace(x2, Var(x), b2), f).map { b =>
            SigmaType(a, Bind(x, b))
          }
        }
      case (RefinementType(a1, Bind(x, p1)), RefinementType(a2, Bind(x2, p2))) =>
        unify(a1, a2, f).map { a =>
          RefinementType(a, Bind(x, f(p1, Tree.replace(x2, Var(x), p2))))
        }
      case (RefinementType(a1, Bind(x, p1)), t3) =>
        unify(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (t3, RefinementType(a1, Bind(x, p1))) =>
        unify(a1, t3, f).map { a =>
          RefinementType(a, Bind(x, p1))
        }
      case (RecType(n, Bind(x1, b1)), RecType(m, Bind(x2, b2))) =>
        unify(b1, Tree.replace(x2, Var(x1), b2), f).map { b =>
          RecType(f(n, m), Bind(x1, b))
        }
      case (EqualityType(t11, t12), EqualityType(t21, t22)) =>
        Some(EqualityType(f(t11, t21), f(t12, t22)))
      case (t1, t2) if t1 == t2 => Some(t1)
      case (_, _) => None
    }
  }

  def ifThenElse(tc: Tree, t1: Tree, t2: Tree): Option[Tree] = {
    if (t1 == t2) Some(t1)
    else unify(t1, t2, (ty1: Tree, ty2: Tree) => IfThenElse(tc, ty1, ty2))
  }

  def matchSimpl(n: Tree, t0: Tree, id: Identifier, tn: Tree): Option[Tree] = {
    unify(t0, tn, (ty0: Tree, tyn: Tree) => Match(n, ty0, Bind(id, tyn)))
  }

  def eitherMatch(n: Tree, idl: Identifier, tl: Tree, idr: Identifier, tr: Tree): Option[Tree] = {
    unify(tl, tr, (tyl: Tree, tyr: Tree) => EitherMatch(n, Bind(idl, tyl), Bind(idr, tyr)))
  }

  def basetype(a: Identifier, t: Tree): Tree = {
    t match {
      case SigmaType(ty1, Bind(x, ty2)) =>
        SigmaType(basetype(a, ty1), Bind(x, basetype(a, ty2)))
      case SumType(ty1, ty2) =>
        SumType(basetype(a, ty1), basetype(a, ty2))
      case ty if a.isFreeIn(ty) => TopType
      case ty => ty
    }
  }

  def spos(a: Identifier, t: Tree): Boolean = {
    t match {
      case NatType => true
      case BoolType => true
      case BottomType => true
      case TopType => true
      case UnitType => true
      case Var(x) if x == a => true
      case t if !a.isFreeIn(t) => true
      case RefinementType(t, _) => spos(a, t)
      case PiType(t1, Bind(x, t2)) => !a.isFreeIn(t1) && spos(a, t2)
      case IntersectionType(t1, Bind(x, t2)) => !a.isFreeIn(t1) && spos(a, t2)
      case PolyForallType(Bind(x, t)) => spos(a, t)
      case SumType(t1, t2) => spos(a, t1) && spos(a, t2)
      case SigmaType(t1, Bind(_, t2)) => spos(a, t1) && spos(a, t2)
      case RecType(_, Bind(x, t)) =>
        spos(a, t) && (!a.isFreeIn(t) || spos(x, t))
      case _ => false
    }
  }

  def dropRefinements(t: Tree): Tree = {
    t match {
      case RefinementType(ty, _) => dropRefinements(ty)
      case _ => t
    }
  }
}
