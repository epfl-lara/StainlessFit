package fit
package core
package codegen.llvm

import core.codegen.utils.LocalHandler

object IR {

  abstract class Instruction

  case class Block(index: Int, label: Label, instructions: List[Instruction]) {
    def <:>(instr: Instruction) = Block(index, label, instructions :+ instr)
    def <:>(is: List[Instruction]) = Block(index, label, instructions ++ is)
  }

  abstract class Name
  case class Label (val label: String) extends Name {
    override def toString: String = s"%$label"
    def printLabel: String = s"$label:"
  }

  case class Local (val name: String) extends Name {
    override def toString: String = s"%$name"
  }

  case class Global (val name: String) extends Name {
    override def toString: String = s"@$name"
  }

  abstract class Type
  case object BooleanType extends Type {
    override def toString(): String =  "i1"
  }
  case object UnitType extends Type {
    override def toString(): String =  "i1"
  }

  case object NatType extends Type {
    override def toString(): String =  "i32"
  }

  case class PairType(firstType: Type, secondType: Type) extends Type
  case class FirstType(nested: Type) extends Type
  case class SecondType(nested: Type) extends Type

  case class EitherType(leftType: Type, rightType: Type) extends Type
  case class LeftType(either: Type) extends Type
  case class RightType(either: Type) extends Type

  case class LambdaType(argType: Type, retType: Type) extends Type
  case class FunctionType(paramType: Type, returnType: Type) extends Type
  case class EnvironmentType(types: List[Type]) extends Type
  case object RawEnvType extends Type //i8*

  case class ParamDef(tpe: Type, local: Local)

  case class Value(val v: Either[Name, Literal])
  object Value {
    def apply(name: Name): Value = new Value(Left(name))
    def apply(literal: Literal): Value = new Value(Right(literal))
  }

  abstract class Literal extends Instruction
  case class BooleanLiteral(b: Boolean) extends Literal
  case class Nat(n: BigInt) extends Literal
  case object UnitLiteral extends Literal
  case object NullLiteral extends Literal

  //Boolean operations
  abstract class Op extends Instruction {
    def returnType: Type
  }

  abstract class BooleanOperator extends Op {
    override def returnType: Type = BooleanType
  }

  abstract class ComparisonOperator extends Op {
    override def toString(): String = "icmp "
    override def returnType: Type = BooleanType
  }

  abstract class NatOperator extends Op {
    override def returnType: Type = NatType
  }

  case object And extends BooleanOperator {
    override def toString: String = "and"
  }
  case object Or extends BooleanOperator {
    override def toString: String = "or"
  }
  case object Not extends BooleanOperator {
    override def toString: String = "fneg"
  }

  case object Neq extends ComparisonOperator {
    override def toString: String = super.toString + "ne"
  }
  case object Eq extends ComparisonOperator {
    override def toString: String = super.toString + "eq"
  }
  case object Lt extends ComparisonOperator {
    override def toString: String = super.toString + "slt"
  }
  case object Gt extends ComparisonOperator {
    override def toString: String = super.toString + "sgt"
  }
  case object Leq extends ComparisonOperator {
    override def toString: String = super.toString + "sle"
  }
  case object Geq extends ComparisonOperator {
    override def toString: String = super.toString + "sge"
  }

  case object Plus extends NatOperator {
    override def toString: String = "add"
  }
  case object Minus extends NatOperator {
    override def toString: String = "sub"
  }
  case object Mul extends NatOperator {
    override def toString: String = "mul"
  }
  case object Div extends NatOperator {
    override def toString: String = "sdiv"
  }

  case class Variable(local: Local) extends Instruction

  case class BinaryOp(op: Op, result: Local, lhs: Value, rhs: Value) extends Instruction
  case class UnaryOp(op: Op, result: Local, operand: Value) extends Instruction

  case class Phi(res: Local, typee: Type, candidates: List[(Local, Label)]) extends Instruction
  case class Assign(result: Local, typee: Type, from: Value) extends Instruction

  case class Call(res: Local, returnType: Type, function: Name, args: List[Value], argTypes: List[Type], env: Value) extends Instruction

  //Terminator instructions
  case class Branch(condition: Value, ifTrue: Label, ifFalse: Label) extends Instruction
  case class Jump(destination: Label) extends Instruction
  case class Return(result : Value, typee: Type) extends Instruction
  case object Exit extends Instruction

  //Memory instructions
  case class Store(value: Value, tpe: Type, ptr: Local) extends Instruction
  case class Load(result: Local, tpe: Type, ptr: Local) extends Instruction

  case class GepToIdx(result: Local, tpe: Type, ptr: Value, idx: Option[Int]) extends Instruction
  case class Malloc(result: Local, temp: Local, tpe: Type) extends Instruction
  case class Bitcast(result: Local, local: Local, toType: Type) extends Instruction

  //Pretty printing instructions
  case class PrintNat(value: Value) extends Instruction
  case class PrintBool(bool: Local) extends Instruction

  case object PrintOpen extends Instruction
  case object PrintClose extends Instruction
  case object PrintComma extends Instruction
  case object PrintLeft extends Instruction
  case object PrintRight extends Instruction
  case class PrintError(msg: String, errLocal: Local) extends Instruction
}
