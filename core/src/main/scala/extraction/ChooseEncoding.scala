package stainlessfit
package core
package extraction

import util.RunContext
import parser.FitParser
import trees._

import typechecker.ScalaDepSugar._

class ChooseEncoding(implicit val rc: RunContext) extends Phase[Unit] {

  def transform(t: Tree): (Tree, Unit) = (encode(LNil(), 0, t)._1, ())

  def encode(path: Tree, n: Int, ts: Seq[Tree]): (Seq[Tree], Int) = {
    (ts.zipWithIndex.map {
      case (t, i) => encode(LCons(NatLiteral(n + i), path), 0, t)._1
    }, n + ts.length)
  }

  def encodeAnnot(n: Int, ty: Tree): (Tree, Int) = {
    val path = Identifier.fresh("p")
    val (nTy, n2) = encode(Var(path), n, ty)
    if (path.isFreeIn(nTy))
      (ExistsType(Choose.PathType, Bind(path, nTy)), n2)
    else
      (nTy, n2)
  }

  def encode(path: Tree, n: Int, t: Tree): (Tree, Int) = t match {
    case Var(x) => (t, n)
    case UnitLiteral => (t, n)
    case NatLiteral(_) => (t, n)
    case BooleanLiteral(_) => (t, n)

    case `LList` => (t, n)
    case TopType => (t, n)
    case NatType => (t, n)
    case UnitType => (t, n)
    case BoolType => (t, n)
    case LNil() => (t, n)

    case Choose(ty) =>
      // TODO: Lift this restriction?
      assert(ty match {
        case `LList` | TopType | NatType | UnitType | BoolType => true
        case _ => false
      })
      (ChooseWithPath(ty, path), n)

    case FixWithDefault(ty, Bind(id, t), td, f) =>
      val (nTy, n2) = encodeAnnot(n, ty)
      val (Seq(nT, nTd), n3) = encode(path, n2, Seq(t, td))
      (FixWithDefault(nTy, Bind(id, nT), nTd, f), n3)

    case SingletonType(ty, t) =>
      val (Seq(nTy, nt), n2) = encode(path, n, Seq(ty, t))
      (SingletonType(nTy, nt), n2)

    case LCons(t1, t2) =>
      val (Seq(nt1, nt2), n2) = encode(path, n, Seq(t1, t2))
      (LCons(nt1, nt2), n2)

    case SigmaType(ty1, Bind(id, ty2)) =>
      val (Seq(nty1, nty2), n2) = encode(path, n, Seq(ty1, ty2))
      (SigmaType(nty1, Bind(id, nty2)), n2)

    case PiType(ty1, Bind(id, ty2)) =>
      val (Seq(nty1, nty2), n2) = encode(path, n, Seq(ty1, ty2))
      val newPathId = Identifier.fresh("p")
      (PiType(Choose.PathType, Bind(newPathId, PiType(nty1, Bind(id, nty2)))), n2)

    case NatMatch(t, t0, Bind(id, ts)) =>
      val (Seq(nt, nt0, nts), n2) = encode(path, n, Seq(t, t0, ts))
      (NatMatch(nt, nt0, Bind(id, nts)), n2)

    case EitherMatch(t, Bind(id1, t1), Bind(id2, t2)) =>
      val (Seq(nt, nt1, nt2), n2) = encode(path, n, Seq(t, t1, t2))
      (EitherMatch(nt, Bind(id1, nt1), Bind(id2, nt2)), n2)

    case ListMatch(t, t1, Bind(idHead, Bind(idTail, t2))) =>
      val (Seq(nt, nt1, nt2), n2) = encode(path, n, Seq(t, t1, t2))
      (ListMatch(nt, nt1, Bind(idHead, Bind(idTail, nt2))), n2)

    case LetIn(None, v, Bind(id, body)) =>
      val (Seq(nV, nBody), n2) = encode(path, n, Seq(v, body))
      (LetIn(None, nV, Bind(id, nBody)), n2)

    case LetIn(Some(ty), v, Bind(id, body)) =>
      val (nTy, n2) = encodeAnnot(n, ty)
      val (Seq(nV, nBody), n3) = encode(path, n2, Seq(v, body))
      (LetIn(Some(nTy), nV, Bind(id, nBody)), n3)

    case App(t1, t2) =>
      val (nt1, n1) = encode(path, n+2, t1)
      val (nt2, n2) = encode(LCons(NatLiteral(n), path), n1, t2)
      (App(App(nt1, LCons(NatLiteral(n+1), path)), nt2), n2)

    case Lambda(optTy, Bind(id, body)) =>
      val pIdent = Identifier.fresh("p")
      val p = Var(pIdent)
      val nOptTy = optTy.map(ty => encodeAnnot(n+1, ty))
      val (nBody, n2) = encode(p, nOptTy.map(_._2).getOrElse(n), body)

      (Lambda(Some(Choose.PathType), Bind(pIdent,
        Lambda(nOptTy.map(_._1), Bind(id,
          nBody
        ))
      )), n2)

    case Pair(t1, t2) =>
      val (Seq(nT1, nT2), n2) = encode(path, n, Seq(t1, t2))
      (Pair(nT1, nT2), n2)

    case First(t) =>
      val (nt, nn) = encode(path, n, t)
      (First(nt), nn)

    case Second(t) =>
      val (nt, nn) = encode(path, n, t)
      (Second(nt), nn)

    case LConsType(ty1, ty2) =>
      val (Seq(nTy1, nTy2), n2) = encode(path, n, Seq(ty1, ty2))
      (LConsType(nTy1, nTy2), n2)
  }
}
