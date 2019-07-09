import trees._
import interpreter._
import printer._
import stainless.annotation._
import stainless.collection._
import stainless.lang._

import scallion.parsing._
import scallion.input._
import scallion.lexing._

import parser.ScalaParser
import parser.ScalaLexer

object Main {

  def main(args: Array[String]): Unit = {
    val ite = """
    (1, 2, 3, 4)
    """.toIterator
    val it = """def f(x: Int): Int = { 4 }
    def fac(n: Int): Int = {
      if(n == 0) { 1 } else { fac (n - 1) * n }
    }

    def sumAcc(acc: Int): Int = {
      fun y: Unit + Nat => {
        match y {
          case Left(x) => acc
          case Right(v) => sumAcc (v + acc)
        }
      }
    }

    val s = fix(sumAcc =>
      fun acc : Int => {
        fun v : Unit + Int => {
          match v {
            case Left(x) => acc
            case Right(n) => sumAcc()(n + acc)
          }
        }
      }
    ) in

    def sumAcc_(acc: Int, y: Unit + Nat): Int = {
      match y {
        case Left(x) => acc
        case Right(v) => sumAcc_(v + acc)
      }
    }

    val x = (a, b, c, d) in
    val sum = sumAcc_(0) in
    val y = sum Right(2) Right(7) Left(2) in
    val z = fac(4) in

    def g(x: Int, y: Int, z: Int, t: Bool, n: Int): Int = {
      if(t) { x + z}
      else { y}
    }

    val t = ((g 1 2 3 false 4) == 3) && y == 12 in
    z

  """.toIterator
    println(ScalaParser.expression.conflicts)
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        println(Printer.pprint(value))
        println("\nIs evaluated into...\n")
        println(Printer.pprint(Interpreter.evaluate(value, 1000)))
      case t => println(t)
    }
  }
}
