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
    val sum = \s(0)
    val y = \sum(Right(2), Right(7), Left(2))
    val z = \\\sum(Right(2))(Right(7))(Left(2))
    ((y + z == 2 * z) && !true || true)
  """.toIterator

    apply(ScalaLexer.apply(it)) match  {
      case Parsed(value, _) =>
        println(Printer.pprint(value))
        println("\nIs evaluated to...\n")
        println(Printer.pprint(Interpreter.evaluate(value, 1000)))
      case t => println(t)
    }
  }
}
