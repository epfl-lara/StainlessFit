package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.Function
import scala.collection.mutable
import trees.Identifier

class FunctionHandler(val rc: RunContext) {

  private val functions = mutable.Map[Identifier, Function]()

  private def getFunction(funId: Identifier) =
    functions.getOrElse(funId, rc.reporter.fatalError(s"Unknown function $funId"))

  def getReturnType(funId: Identifier) =
    getFunction(funId).returnType

  def getArgType(funId: Identifier, arg: Int) =
    getFunction(funId).params(arg).tpe

  def add(funId: Identifier, fun: Function) =
    functions.put(funId, fun)
}
