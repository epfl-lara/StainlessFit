package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.IR._
import codegen.llvm._
import scala.collection.mutable
import trees.{Identifier => SfIdentifier}

class LocalHandler(val rc : RunContext) {

  private val counter = new codegen.utils.UniqueCounter[String]
  private var blockIndex : Int = -1

  private val variables = mutable.Map[SfIdentifier, ParamDef]()

  def add(id: SfIdentifier, param: ParamDef): Unit = {
    variables.put(id, param)
  }

  def add(args: List[(SfIdentifier, ParamDef)]): Unit = {
    args.foreach(tuple => add(tuple._1, tuple._2))
  }

  def get(id: SfIdentifier): ParamDef =
    variables.getOrElse(id, rc.reporter.fatalError(s"Unkown variable $id"))

  def getType(id: SfIdentifier) = get(id).tpe
  def getLocal(id: SfIdentifier) = get(id).local

  def newBlock(name: String): Block = {
    blockIndex += 1
    Block(blockIndex, freshLabel(name), Nil)
  }

  def newBlock(label: Label): Block = {
    blockIndex += 1
    Block(blockIndex, label, Nil)
  }

  def freshLocal(name: String): Local = {
    new Local(name + counter.next(name))
  }

  def freshLocal(id: SfIdentifier): Local = {
    new Local(id.toString)
  }

  def freshLocal(): Local = freshLocal("local")

  def freshLabel(name: String): Label = {
    new Label(name + counter.next(name))
  }

  def freshLabel(id: SfIdentifier): Label = {
    new Label(id.toString)
  }

  def freshLabel(): Label = freshLabel("")

  def freshGlobal(name: String): Global = {
    new Global(name + counter.next(name))
  }

  def freshGlobal(id: SfIdentifier): Global = {
    new Global(id.toString)
  }

  def freshGlobal(): Global = freshGlobal("global")
}
