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

    case Choose(ty) => (App(Choose(ty), path), n)

    case FixWithDefault(ty, Bind(id, t), td) =>
      val (Seq(nTy, nT, nTd), n2) = encode(path, n, Seq(ty, t, td))
      (FixWithDefault(nTy, Bind(id, nT), nTd), n2)

    case SingletonType(ty, t) =>
      val (Seq(nTy, nt), n2) = encode(path, n, Seq(ty, t))
      (SingletonType(nTy, nt), n2)

    case LCons(t1, t2) =>
      val (Seq(nt1, nt2), n2) = encode(path, n, Seq(t1, t2))
      (LCons(nt1, nt2), n2)

    case PiType(ty1, Bind(id, ty2)) =>
      val path = Identifier.fresh("p")
      val (Seq(nty1, nty2), n2) = encode(Var(path), n, Seq(ty1, ty2))
      (PiType(LList, Bind(path, PiType(nty1, Bind(id, nty2)))), n2)

    case NatMatch(t, t0, Bind(id, ts)) =>
      val (Seq(nt, nt0, nts), n2) = encode(path, n, Seq(t, t0, ts))
      (NatMatch(nt, nt0, Bind(id, nts)), n2)

    case LetIn(None, v, Bind(id, body)) =>
      val (Seq(nV, nBody), n2) = encode(path, n, Seq(v, body))
      (LetIn(None, nV, Bind(id, nBody)), n2)

    case LetIn(Some(ty), v, Bind(id, body)) =>
      val (Seq(nTy, nV, nBody), n2) = encode(path, n, Seq(ty, v, body))
      (LetIn(Some(nTy), nV, Bind(id, nBody)), n2)

    case App(t1, t2) =>
      val (nt1, n1) = encode(path, n+2, t1)
      val (nt2, n2) = encode(LCons(NatLiteral(n), path), n1, t2)
      (App(App(nt1, LCons(NatLiteral(n+1), path)), nt2), n2)

    case Lambda(optTy, Bind(id, body)) =>
      val pIdent = Identifier.fresh("p")
      val p = Var(pIdent)
      val nOptTy = optTy.map(ty => encode(LCons(NatLiteral(n), p), n+1, ty))
      val (nBody, n2) = encode(p, nOptTy.map(_._2).getOrElse(n), body)

      (Lambda(Some(LList), Bind(pIdent,
        Lambda(nOptTy.map(_._1), Bind(id,
          nBody
        ))
      )), n2)
  }
}
