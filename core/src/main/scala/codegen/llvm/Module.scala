package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ArrayBuffer

case class Module(name: String, blocks: ArrayBuffer[Block], functions: ArrayBuffer[Function]) {

  import java.io.{File, FileWriter}

  def printToFile(filename: String) = {
    val writer = new FileWriter(new File(filename))
    writer.write(ModulePrinter(this))
    writer.flush()
  }

  def add(block: Block): Unit = blocks += block
}

object Module {
  def apply(name: String): Module = Module(name, ArrayBuffer.empty[Block], ArrayBuffer.empty[Function])
}

class TargetTriple {
  //TODO
}
