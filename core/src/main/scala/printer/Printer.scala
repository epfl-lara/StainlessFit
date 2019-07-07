package printer

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import _root_.trees._

object Printer {

  def pprint(e: Tree): String = {
    e match {
      case Var(id, x) => x
      case UnitLiteral => "unit"
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
      case Lambda(tp, bind) =>
        s"""fun ${pprint(bind)}"""
      case App(e1, e2) => s"${pprint(e1)}(${pprint(e2)})"
      case Fix(_, Bind(_, body)) =>
      s"""Fix(
       |  ${pprint(body).replaceAll("\n", "\n  ")}
       |)""".stripMargin
      case LeftTree(b) => s"Left(${pprint(b)})"
      case RightTree(b) => s"Right(${pprint(b)})"

      case EitherMatch(t, Bind(Some(x), t1), Bind(Some(y), t2)) =>
        val ts = pprint(t)
        val t1s = pprint(t1).replaceAll("\n", "\n    ")
        val t2s = pprint(t2).replaceAll("\n", "\n    ")
        s"""${ts} match {
        |  case Left(${pprint(x)}) =>
        |    ${t1s}
        |  case Right(${pprint(y)}) =>
        |    ${t2s}
        |}""".stripMargin
      case Bind(Some(Var(_, x)), b) =>

        s"""${x} => {
        |  ${pprint(b).replaceAll("\n", "\n  ")}
        |}""".stripMargin
      case Bind(None(), b) => s"""unit => {
        |  ${pprint(b).replaceAll("\n", "\n  ")}
        |}""".stripMargin
      case LetIn(tp, v, Bind(Some(x), b)) =>
          val tv = pprint(v)
          val tx = pprint(x)
          val tb = pprint(b)
          s"""val ${tx} = ${tv}
          |${tb}""".stripMargin
      case Primitive(op, arg::Nil())  => s"${op}${pprint(arg)}"
      case Primitive(op, arg1::arg2::Nil())  => s"(${pprint(arg1)}) ${op} (${pprint(arg2)})"

      case Pair(a, b) => s"(${pprint(a)}, ${pprint(b)})"
      case First(b) => s"First(${pprint(b)})"
      case Second(b) => s"Second(${pprint(b)})"
      case Match(t, t1, t2) =>
        val ts = pprint(t)
        val t1s = pprint(t1).replaceAll("\n", "\n    ")
        val t2s = pprint(t2).replaceAll("\n", "\n  ")
        s"""${ts} match {
        |  case 0 =>
        |    ${t1s}
        |  case ${t2s}
        |}""".stripMargin
      case _ => "<not yet pprint>"
    }
  }
}