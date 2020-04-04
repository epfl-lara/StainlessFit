package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.IR._
import codegen.llvm._
import scala.collection.mutable
//import codegen.utils.{Identifier => LLVMIdentifier, _}

class LocalHandler(val rc : RunContext) {

  private val counter = new codegen.utils.UniqueCounter[String]
  private var blockIndex : Int = -1

  private val variables = mutable.Map[Identifier, Local]()

  def add(id: Identifier, local: Local): Unit = {
    variables.put(id, local)
  }

  def newBlock(name: String): Block = {
    blockIndex += 1
    Block(blockIndex, freshLabel(name), Nil)
  }


  def get(id: Identifier) = variables.get(id).orElse(rc.reporter.fatalError(s"Unkown variable $id"))

  def freshLocal(name: String): Local = {
    new Local(name + counter.next(name))
  }

  def freshLocal(id: Identifier): Local = {
    new Local(id.toString)
  }

  def freshLocal(): Local = freshLocal("")

  def freshLabel(name: String): Label = {
    new Label(name + counter.next(name))
  }

  def freshLabel(id: Identifier): Label = {
    new Label(id.toString)
  }

  def freshLabel(): Label = freshLabel("")
}
