package stainlessfit
package core
package codegen.llvm

import core.codegen.utils._
import core.codegen.llvm.IR._
import scala.collection.mutable.ArrayBuffer

abstract class Function {
  val returnType: Type
  val name: Global
  val params: List[ParamDef]
  val blocks: ArrayBuffer[Block]

  def add(block: Block): Unit = blocks += block
  def defaultEnv(): Value = Value(NullLiteral)
  def envSize(): Int = 0
}

case class TopLevelFunction(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block]) extends Function

case class Lambda(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block], size: Int) extends Function {
  override def defaultEnv(): Value = Value(Local("raw.env"))
  override def envSize(): Int = size
}

object CreateFunction {
  def apply(tpe: Type, name: Global, params: List[ParamDef]): Function = {
    TopLevelFunction(tpe, name, params, ArrayBuffer.empty[Block])
  }
}

object CreateLambda {
  def apply(tpe: Type, name: Global, params: List[ParamDef], envSize: Int): Function = {
    Lambda(tpe, name, params, ArrayBuffer.empty[Block], envSize)
  }
}

object CreateMain {
  def apply(name: Global): Function = {
    TopLevelFunction(NatType, name, Nil, ArrayBuffer.empty[Block])
  }
}
