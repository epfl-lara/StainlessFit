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

  private val variables = mutable.Map[String, ParamDef]()

  def add(id: SfIdentifier, param: ParamDef): Unit =
    variables.put(translateId(id), param)

  def add(args: List[(SfIdentifier, ParamDef)]): Unit =
    args.foreach(tuple => add(tuple._1, tuple._2))

  def get(id: SfIdentifier): ParamDef =
    variables.getOrElse(translateId(id), rc.reporter.fatalError(s"Unkown variable $id"))

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

  def freshLocal(name: String): Local = Local(name + counter.next(name))
  def freshLocal(id: SfIdentifier): Local = Local(translateId(id))
  def freshLocal(): Local = freshLocal("local")
  def dot(local: Local, s: String) = freshLocal(s"${local.name}.$s")

  def freshLabel(name: String): Label = Label(name + counter.next(name))
  def freshLabel(id: SfIdentifier): Label = Label(translateId(id))
  def freshLabel(): Label = freshLabel("label")
  def dot(label: Label, s: String) = freshLabel(s"${label.label}.$s")

  def freshGlobal(name: String): Global = Global(name + counter.next(name))
  def freshGlobal(id: SfIdentifier): Global = Global(translateId(id))
  def freshGlobal(): Global = freshGlobal("global")
  def dot(global: Global, s: String) = freshGlobal(s"${global.name}.$s")

  def translateId(id: SfIdentifier): String = id.toString.replace("#", "_")
}
