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
    fun (x: (Unit + Unit)) => { 2 }
    """.toIterator
    val it = """def f(x: Nat): Nat = { 4 }
    def fac(n: Nat): Nat = {
      if(n == 0) { 1 } else { fac (n - 1) * n }
    }

    def sumAcc(acc: Nat): Nat = {
      fun (y: Unit + Nat) => {
        match y {
          case Left(x) => acc
          case Right(v) => sumAcc (v + acc)
        }
      }
    }

    val s = fix[n => Unit + Nat](sumAcc =>
      fun (acc : Nat) => {
        fun (v : Unit + Nat) => {
          match v {
            case Left(x) => acc
            case Right(n) => sumAcc()(n + acc)
          }
        }
      }
    ) in

    def sumAcc_(acc: Nat, y: Unit + Nat): Nat = {
      match y {
        case Left(x) => acc
        case Right(v) => sumAcc_(v + acc)
      }
    }

    val x = (a, b, c, d) in
    val sum = sumAcc_(0) in
    val y = sum Right(2) Right(7) Left(()) in
    val z = fac(4) in

    def g(x: Nat, y: Nat, z: Nat, t: Bool, n: Nat): Nat = {
      if(t) { x + z}
      else { y }
    }

    val t = ((g 1 2 3 false 4) == 3) && y == 12 in

  def f(x: (Nat + Nat) + Nat): Nat = {
    match x {
      case Left(x) =>
        match x {
          case Left(x) => x + 2
          case Right(v) => 1
        }
      case Right(x) => 0
    }
  }

  val x = f(Left(Left(3))) in x
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
