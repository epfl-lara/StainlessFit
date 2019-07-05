package printer

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import _root_.trees._

object Printer {
  def pprint(e: Tree, ind: Int): String = {
    e match {
      case Var(id, x) => x
      case UnitLiteral => ""
      case BoolLiteral(b) => b.toString
      case NatLiteral(n) => n.toString
      case IfThenElse(c, e1, e2) => {
        val cs = pprint(c, 0)
        val e1s = pprint(e1, ind)
        val e2s = pprint(e2, ind)
        s"""${" " * ind}if(${cs}) {
        |  ${e1s}
        |{" " * ind}} else {
        |  ${e2s}
        |${" " * ind}}""".stripMargin
      }
      case Lambda(tp, body) => s"${" " * ind} fun ${pprint(body, ind + 2)}"
      case App(e1, e2) => s"(${pprint(e1, ind)})(${pprint(e2, ind)})"
      case Fix(body) => s"Fix(${pprint(body, ind)})"
      case LeftTree(b) => s"Left(${pprint(b, ind)})"
      case RightTree(b) => s"Rigt(${pprint(b, ind)})"
      case EitherMatch(t, t1, t2) =>
        val ts = pprint(t, ind)
        val t1s = pprint(t1, ind)
        val t2s = pprint(t2, ind)
        s"""${ts} match {
        |  case Left() => ${t1s}
        |  case Right() => ${t2s}
        |}""".stripMargin
      case Bind(Some(Var(_, x)), b) =>
        s"""${x} : {
        |  ${pprint(b, ind)}
        |}""".stripMargin
      case Bind(None(), b) =>
        s"${pprint(b, ind)}"
      case LetIn(tp, v, Bind(Some(x), b)) =>
          val tv = pprint(v, ind)
          val tx = pprint(x, ind)
          val tb = pprint(b, ind)
          s"""Let ${tx} = ${tv} in ${tb}
          """.stripMargin
      case Primitive(op, arg::Nil())  => s"op(${pprint(arg, 0)})"
      case Primitive(op, arg1::arg2::Nil())  => s"op(${pprint(arg1, 0)}, ${pprint(arg2, 0)})"
      case _ => "e"
    }
  }
}