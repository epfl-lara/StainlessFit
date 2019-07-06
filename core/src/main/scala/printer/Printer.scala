package printer

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import _root_.trees._

object Printer {
  def pprint(e: Tree): String = {
    e match {
      case Var(id, x) => x
      case UnitLiteral => "()"
      case BoolLiteral(b) => b.toString
      case NatLiteral(n) => n.toString
      case IfThenElse(c, e1, e2) =>
        val cs = pprint(c)
        val e1s = pprint(e1).replaceAll("\n", "\n  ")
        val e2s = pprint(e2).replaceAll("\n", "\n  ")
        s"""if(${cs}) {
        |  ${e1s}
        |else {
        |  ${e2s}
        |}""".stripMargin
      case Lambda(tp, Bind(Some(x), body)) =>
        s"""fun ${pprint(x)} => {
        |  ${pprint(body).replaceAll("\n", "\n  ")}
        |}""".stripMargin
      case Lambda(tp, Bind(None(), body)) =>
        s"""fun () => {
        |  ${pprint(body).replaceAll("\n", "\n  ")}
        |}""".stripMargin
      case App(e1, e2) => s"(${pprint(e1)})(${pprint(e2)})"
      case Fix(body) =>
      s"""Fix(
       |  ${pprint(body).replaceAll("\n", "\n  ")}
       |)""".stripMargin
      case LeftTree(b) => s"Left(${pprint(b)})"
      case RightTree(b) => s"Rigt(${pprint(b)})"

      case EitherMatch(t, t1, t2) =>
        val ts = pprint(t)
        val t1s = pprint(t1).replaceAll("\n", "\n    ")
        val t2s = pprint(t2).replaceAll("\n", "\n    ")
        s"""${ts} match {
        |  case Left() => {
        |    ${t1s}
        |  }
        |  case Right() => {
        |    ${t2s}
        |  }
        |}""".stripMargin
      case Bind(Some(Var(_, x)), b) =>
        s"""${x} => {
        |  ${pprint(b).replaceAll("\n", "\n  ")}
        |} """.stripMargin
      case Bind(None(), b) => pprint(b)
      case LetIn(tp, v, Bind(Some(x), b)) =>
          val tv = pprint(v)
          val tx = pprint(x)
          val tb = pprint(b)
          s"""val ${tx} = ${tv}
          |${tb}
          """.stripMargin
      case Primitive(op, arg::Nil())  => s"op(${pprint(arg)})"
      case Primitive(op, arg1::arg2::Nil())  => s"op(${pprint(arg1)}, ${pprint(arg2)})"
      case _ => "e"
    }
  }
}