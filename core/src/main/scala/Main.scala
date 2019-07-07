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
    val ii = """def f(x: Int, y: Int) = { 4 }""".toIterator
    val it = """def f(x: Int) = { 4 }

    def fac(n: Int) = {
      if(n == 0) { 1 } else { (\fac(n - 1)) * n }
    }

    def sumAcc(acc: Int) = {
      fun y: Unit + Nat => {
        match y {
          case Left(x) => acc
          case Right(v) => \sumAcc(v + acc)
        }
      }
    }

    val s = fix(sumAcc =>
      fun acc : Int => {
        fun v : Unit + Int => {
          match v {
            case Left(x) => acc
            case Right(n) => \\sumAcc()(n + acc)
          }
        }
      }
    )

    def sumAcc_(acc: Int, y: Unit + Nat) = {
      match y {
        case Left(x) => acc
        case Right(v) => \sumAcc_(v + acc)
      }
    }

    val sum = \sumAcc_(0)
    val y = \sum(Right(2), Right(7), Left(2))
    val z = \\\sum(Right(2))(Right(7))(Left(2))
    val t = ((y + z == 2 * z) && !true || true)
    val z = \fac(4)
    t
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
