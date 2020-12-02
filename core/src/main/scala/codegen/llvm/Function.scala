package fit
package core
package codegen.llvm

import core.codegen.utils._
import core.codegen.llvm.IR._
import scala.collection.mutable.ArrayBuffer

case class Function(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block], recursiveLocal: Local) {
  def add(block: Block): Unit = blocks += block
}

object CreateLambda {
  def apply(tpe: Type, name: Global, params: List[ParamDef], recursiveLocal: Local): Function = {
    Function(tpe, name, params, ArrayBuffer.empty[Block], recursiveLocal)
  }
}

object CreateMain {
  def apply(name: Global): Function = {
    Function(NatType, name, Nil, ArrayBuffer.empty[Block], Local(".main"))
  }
}
