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

  def add(block: Block): Unit
  def defaultArg: Value = Value(NullLiteral)
}

case class TopLevelFunction(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block]) extends Function {

  def add(block: Block): Unit = blocks += block
  // def extraArg: Value = Value(NullLiteral)
  // def extraArgType: Type = RawEnvType
}

case class Lambda(returnType: Type, name: Global, params: List[ParamDef], blocks: ArrayBuffer[Block]) extends Function {
  def add(block: Block): Unit = blocks += block
  override def defaultArg: Value = Value(Local("raw.env"))
}

object CreateFunction {

  def apply(tpe: Type, name: Global, params: List[ParamDef]): Function = {
    // val env = ParamDef(RawEnvType, Local(""))
    TopLevelFunction(tpe, name, params, ArrayBuffer.empty[Block])
  }
}

object CreateLambda {
  def apply(tpe: Type, name: Global, params: List[ParamDef]): Function = {
    // val env = ParamDef(RawEnvType, Local("raw.env"))
    Lambda(tpe, name, params, ArrayBuffer.empty[Block])
  }
}

object CreateMain {
  def apply(name: Global): Function = {
    TopLevelFunction(NatType, name, Nil, ArrayBuffer.empty[Block])
  }
}
