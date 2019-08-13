import trees._
import interpreter._
import typechecker._
import typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object Main {
  def main(args: Array[String]): Unit = {
    Config.parse(args).foreach(App.launch)
  }
}
