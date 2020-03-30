package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm._
import scala.collection.mutable
//import codegen.utils.{Identifier => LLVMIdentifier, _}

class LocalHandler(val rc : RunContext) {

  private val counter = new codegen.utils.UniqueCounter[String]

  private val variables = mutable.Map[Identifier, Local]()

  def add(id: Identifier, local: Local): Unit = {
    variables.put(id, local)
  }

  def get(id: Identifier) = variables.get(id).orElse(rc.reporter.fatalError(s"Unkown variable $id"))

  def freshLocal(name: String) = {
    new Local(name + counter.next(name))
  }

  def freshLocal(id: Identifier) = {
    new Local(id.toString)
  }

  def freshLabel(name: String) = {
    new Label(name + counter.next(name))
  }

  def freshLabel(id: Identifier) = {
    new Label(id.toString)
  }

  def fresh() = freshLocal("")
}
