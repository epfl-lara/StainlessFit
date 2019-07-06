import trees._
import interpreter._
import printer._
import stainless.annotation._
import stainless.collection._
import stainless.lang._

import scallion.parsing._
import scallion.input._
import scallion.lexing._

import parser.ScalaParser._
import parser.ScalaLexer

object Main {


  def main(args: Array[String]): Unit = {
    val it = """val s = fix(sumAcc =>
      fun acc => {
        fun v => {
          match v {
            case Left(x) => acc
            case Right(n) => \\sumAcc()(n + acc)
          }
        }
      }
    )
    in
    val sum = \s(0) in
    val y = \sum(Right(2), Right(7), Left(2)) in
    (22)
    """.toIterator

    apply(ScalaLexer.apply(it)) match  {
      case Parsed(value, _) =>
        println(Printer.pprint(value))
        //println(value)
        //val v = App(App(App(value, RightTree(NatLiteral(1))), RightTree(NatLiteral(3))), LeftTree(UnitLiteral))
        //println(Printer.pprint(Interpreter.evaluate(v, 1000), 0))
        println(Interpreter.evaluate(value, 1000))
      case t => println(t)
    }
  }
}
