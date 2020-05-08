package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.Function
import codegen.llvm.IR._
import scala.collection.mutable
import trees.Identifier

class FunctionHandler(val rc: RunContext) {

  // private val functions = mutable.Map[Identifier, Function]()
  // private val lambdas = mutable.Map[Identifier, Function]()
  private val lambdas = mutable.ArrayBuffer[Identifier]()
  private val functions = mutable.ArrayBuffer[Identifier]()

  private var lambdaIndex : Int = -1
  var lambdaToConvert: Identifier = null;

  private val recorded = mutable.Map[Identifier, Function]()

  def add(id: Identifier, fun: Function) =
    recorded.put(id, fun)

  def get(id: Identifier) = {
    recorded.getOrElse(id, unknownId(id))
  }

  private def unknownId(id: Identifier) =
    rc.reporter.fatalError(s"Identifier $id doesn't match any known functions or lambdas")

  def addFunction(funId: Identifier, fun: Function) = {
    add(funId, fun)
    functions += funId
  }

  def addLambda(lambdaId: Identifier, lambda: Function) = {
      add(lambdaId, lambda)
      lambdas += lambdaId
  }

  //Has
  def hasFunction(id: Identifier): Boolean =
    functions.contains(id)

  def hasLambda(id: Identifier): Boolean =
    lambdas.contains(id)

  // //Get
  // def getFunction(funId: Identifier) =
  //   recorded.getOrElse(funId, rc.reporter.fatalError(s"Unknown function $funId"))
  //
  // def getLambda(lambdaId: Identifier) =
  //   recorded.getOrElse(lambdaId, rc.reporter.fatalError(s"Unknown lambda $lambdaId"))

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

  def getLambdas() = recorded.filter{case (key, value) => hasLambda(key)}.values.toList //recorded.filter(hasLambda(_)).map()

  def nextLambda(id: Identifier) = {
    lambdaIndex += 1
    // s"${lambda.name}.$lambdaIndex"
    id.toString.replace("#", "_") + s".lambda$lambdaIndex"
  }
}
