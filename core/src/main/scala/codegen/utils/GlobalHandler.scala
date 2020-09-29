package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.Function
import codegen.llvm.IR._
import scala.collection.mutable
import trees.Identifier

class GlobalHandler(val rc: RunContext) {

  private val lambdas = mutable.ArrayBuffer[Function]()

  def getLambdas() = lambdas.toList

  def addLambda(lambda: Function) = {
    lambdas += lambda
  }

  //Lambda naming ==============================================================
  private var nameAfter: List[(Identifier, Int)] = Nil

  def nameLambdasAfter(name: Identifier) = {
    nameAfter = (name, -1) +: nameAfter
  }

  def stopNamingAfter(name: Identifier) = {
    if(name != nameAfter.head._1){
      rc.reporter.fatalError(s"Error while naming lambdas")
    } else {
      nameAfter = nameAfter.tail
    }
  }

  def nextLambdaId(): Identifier = {
    val (base, index) = nameAfter.head
    val next = if(index == -1){
      base
    } else {
      Identifier(0, base.name + "_" + index)
    }
    nameAfter = (base, index + 1) +: nameAfter.tail
    next
  }

  //Global naming ==============================================================
  private val counter = new codegen.utils.UniqueCounter[String]

  def nextIndex(name: String): String = counter.next(name) match {
    case -1 => ""
    case idx => s"$idx"
  }

  def freshGlobal(name: String): Global = Global(name + nextIndex(name))
  def freshGlobal(id: Identifier): Global = freshGlobal(id.name)
  def freshGlobal(): Global = freshGlobal("global")
  def dot(global: Global, s: String) = freshGlobal(s"${global.name}.$s")
}
