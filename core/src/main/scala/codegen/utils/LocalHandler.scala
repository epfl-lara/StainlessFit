package stainlessfit
package core
package codegen.utils

import util.RunContext
import codegen.llvm.IR._
import codegen.llvm._
import scala.collection.mutable
import trees.Identifier

class LocalHandler(val rc : RunContext) {

  private val counter = new codegen.utils.UniqueCounter[String]
  private var blockIndex : Int = -1

  private val variables = mutable.Map[String, ParamDef]()

  def add(id: Identifier, param: ParamDef): Unit =
    variables.put(translateId(id), param)

  def add(args: List[(Identifier, ParamDef)]): Unit =
    args.foreach(tuple => add(tuple._1, tuple._2))

  def get(id: Identifier): ParamDef =
    variables.getOrElse(translateId(id), rc.reporter.fatalError(s"Unkown variable $id"))

  def getType(id: Identifier) = get(id).tpe
  def getLocal(id: Identifier) = get(id).local

  def newBlock(name: String): Block = {
    blockIndex += 1
    Block(blockIndex, freshLabel(name), Nil)
  }

  def newBlock(label: Label): Block = {
    blockIndex += 1
    Block(blockIndex, label, Nil)
  }

  def nextIndex(name: String): String = counter.next(name) match {
    case -1 => ""
    case idx => s"$idx"
  }

  def freshLocal(name: String): Local = Local(name + nextIndex(name))
  def freshLocal(id: Identifier): Local = freshLocal(id.name)
  def freshLocal(): Local = freshLocal("local")
  def dot(local: Local, s: String) = freshLocal(s"${local.name}.$s")

  def freshLabel(name: String): Label = Label(name + nextIndex(name))
  def freshLabel(id: Identifier): Label = freshLabel(id.name)
  def freshLabel(): Label = freshLabel("label")
  def dot(label: Label, s: String) = freshLabel(s"${label.label}.$s")

  def translateId(id: Identifier): String = id.toString.replace("#", "_")
}
