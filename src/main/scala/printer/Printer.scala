package printer

import _root_.trees._

object Printer {
  def pprint(e: Tree): String = {
    e match {
      case Var(id, x) => x
      case BoolLiteral(b) => b.toString
      case NatLiteral(n) => n.toString
      case IfThenElse(c, e1, e2) => {
        val cs = pprint(c)
        val e1s = pprint(e1)
        val e2s = pprint(e2)
        s"""if(${cs}) {
        |  ${e1s}
        |} else {
        |  ${e2s}
        |}""".stripMargin
      }
      case Lambda(tp, body) => s"fun ${pprint(body)}"
      case App(e1, e2) => s"(${pprint(e1)})(${pprint(e2)})"
      case Fix(body) => s"Fix(${pprint(body)})"
      case EitherMatch(t, t1, t2) =>
        val ts = pprint(t)
        val t1s = pprint(t1)
        val t2s = pprint(t2)
        s"""${ts} match {
        |  case Left() => ${t1s}
        |  case Right() => ${t2s}
        |}""".stripMargin
      case Bind(Var(id, x), b) =>
        s"""${x} : {
        |  ${pprint(b)}
        |}""".stripMargin
      case _ => "e"
    }
  }
}