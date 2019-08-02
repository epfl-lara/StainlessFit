package printer

import stainless.annotation._
import stainless.collection._
import stainless.lang._

import trees._

object Printer {

  def pprint(e: Tree, inline: Boolean = false, bindType: Option[Tree] = None()): String = {
    e match {
      case Var(id) => id.toString
      case UnitLiteral => "unit"
      case BoolLiteral(b) => b.toString
      case NatLiteral(n) => n.toString
      case IfThenElse(c, e1, e2) =>
        val cs = pprint(c)
        val e1s = pprint(e1).replaceAll("\n", "\n  ")
        val e2s = pprint(e2).replaceAll("\n", "\n  ")
        s"""if(${cs}) {
        |  ${e1s}
        |}
        |else {
        |  ${e2s}
        |}""".stripMargin
      case Lambda(tp, bind) =>
        val pBind = pprint(bind, bindType = tp)
        s"fun ${pBind}"
      case App(e1, e2) => s"${pprint(e1)}(${pprint(e2)})"
      case Fix(_, Bind(_, body)) =>
      s"""Fix(
       |  ${pprint(body).replaceAll("\n", "\n  ")}
       |)""".stripMargin
      case LeftTree(b) => s"Left(${pprint(b)})"
      case RightTree(b) => s"Right(${pprint(b)})"

      case EitherMatch(t, Bind(x, t1), Bind(y, t2)) =>
        val ts = pprint(t)
        val t1s = pprint(t1).replaceAll("\n", "\n    ")
        val t2s = pprint(t2).replaceAll("\n", "\n    ")
        s"""${ts} match {
        |  case Left(${x.name}) =>
        |    ${t1s}
        |  case Right(${y.name}) =>
        |    ${t2s}
        |}""".stripMargin
      case Bind(Identifier(_, x), b) =>
        val pType = bindType match { case None() => "" case Some(t) => s": ${pprint(t)}"}
        if(inline) s"${x}${pType} => { ${pprint(b).replaceAll("\n", "\n  ")} }"
        else s"${x}${pType} => {\n  ${pprint(b).replaceAll("\n", "\n  ")}\n}"
      case LetIn(tp, v, Bind(x, b)) =>
        val tv = pprint(v)
        val tx = x.name
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


      case NatType => "Nat"
      case BoolType => "Bool"
      case UnitType => "Unit"
      case SumType(t1, t2) => s"(${pprint(t1)}) + (${pprint(t2)})"
      case PiType(t1, Bind(n, t2)) =>
        if(Tree.appearsFreeIn(n, t2)) s"(${n}: ${pprint(t1)}) => (${pprint(t2)})"
        else s"(${pprint(t1)}) => (${pprint(t2)})"
      case SigmaType(t1, Bind(n, t2)) =>
        if(Tree.appearsFreeIn(n, t2)) s"(${n}: ${pprint(t1)}, ${pprint(t2)})"
        else s"(${pprint(t1)}, ${pprint(t2)})"
      case IntersectionType(t1, Bind(n, t2)) => s"∀${n}: ${pprint(t1)}. (${pprint(t2)})"
      case RefinementType(t1, Bind(n, t2)) => s"{${n}: ${pprint(t1)}, ${pprint(t2)}}"
      case _ => s"<not yet pprint> ${e.getClass}"
    }
  }
}