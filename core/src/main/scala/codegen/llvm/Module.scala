package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ArrayBuffer

case class Module(name: String, main: Function, functions: List[Function]) {
  //TODO add external functions
  import java.io.{File, FileWriter}

  def printToFile(filename: String) = {
    val writer = new FileWriter(new File(filename))
    writer.write(ModulePrinter(this))
    writer.flush()
  }

  def add(block: Block): Unit = main.add(block)
}

// object Module {
//   def apply(name: String): Module =
//     //Module(name, Function.main(tpe), ArrayBuffer.empty[Function])
//     Module(name, Function.main(tpe), Nil)
// }

class TargetTriple {
  //TODO
}
