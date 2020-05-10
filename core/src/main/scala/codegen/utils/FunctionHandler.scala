package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.Function
import codegen.llvm.IR._
import scala.collection.mutable
import trees.Identifier

class FunctionHandler(val rc: RunContext) {

  private val counter = new codegen.utils.UniqueCounter[String]

  private val lambdas = mutable.ArrayBuffer[Identifier]()
  private val functions = mutable.ArrayBuffer[Identifier]()
  private val recorded = mutable.Map[Identifier, Function]()
  private val inverse = mutable.Map[Function, Identifier]()

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

  def add(id: Identifier, fun: Function) = {
    recorded.put(id, fun)
    inverse.put(fun, id)
  }

  def get(id: Identifier) = {
    recorded.getOrElse(id, unknownId(id))
  }

  def getId(fun: Function) = {
    inverse.getOrElse(fun, unknownFunction(fun))
  }

  private def unknownId(id: Identifier) =
    rc.reporter.fatalError(s"Identifier $id doesn't match any known functions or lambdas")

  private def unknownFunction(fun: Function) =
    rc.reporter.fatalError(s"Unknown function ${fun.name}")

  def addFunction(funId: Identifier, fun: Function) = {
    add(funId, fun)
    functions += funId
  }

  def addLambda(lambdaId: Identifier, lambda: Function) = {
      add(lambdaId, lambda)
      lambdas += lambdaId
  }

  def addMain(mainId: Identifier, main: Function) = {
    inverse.put(main, mainId)
  }

  def hasFunction(id: Identifier): Boolean =
    functions.contains(id)

  def hasLambda(id: Identifier): Boolean =
    lambdas.contains(id)

  def getArgNumber(id: Identifier) = {
    if(hasLambda(id)){
      1
    } else {
      get(id).params.size
    }
  }

  def getReturnType(id: Identifier) =
    get(id).returnType

  def getArgType(id: Identifier, arg: Int) =
    get(id).params(arg).tpe

  def getGlobal(id: Identifier) =
    get(id).name

  def getDefaultArg(id: Identifier) = {
    get(id).defaultArg
  }

  // def getExtraArgType(id: Identifier) = {
  //   get(id).extraArgType
  // }

  def getLambdas() = recorded.filter{case (key, value) => hasLambda(key)}.values.toList
  def getFunctions() = recorded.filter{case (key, value) => hasFunction(key)}.values.toList

  def nextLambda(): Identifier = {
    val (base, index) = nameAfter.head
    val next = if(index == -1){
      base
    } else {
      Identifier(0, base.name + "_" + index)
    }
    nameAfter = (base, index + 1) +: nameAfter.tail
    next
  }

  def nextIndex(name: String): String = counter.next(name) match {
    case -1 => ""
    case idx => s"$idx"
  }

  def freshGlobal(name: String): Global = Global(name + nextIndex(name))
  def freshGlobal(id: Identifier): Global = freshGlobal(id.name)
  def freshGlobal(): Global = freshGlobal("global")
  def dot(global: Global, s: String) = freshGlobal(s"${global.name}.$s")
}
