package stainlessfit
package core
package codegen.llvm

import core.codegen.utils._
import core.codegen.llvm.IR._
import scala.collection.mutable.ArrayBuffer

case class Function(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block]) {

  def add(block: Block): Unit = blocks += block

  override def toString(): String = {
    s"Function $name"
  }
}

object Function {
  def main(tpe: Type) = {
    Function(tpe, new Global("main"), Nil, ArrayBuffer.empty[Block])
  }

  def apply(tpe: Type, name: Global, params: List[ParamDef]): Function = {
    Function(tpe, name, params, ArrayBuffer.empty[Block])
  }
}
