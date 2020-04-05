package stainlessfit
package core
package codegen.llvm

object IR {

  abstract class Instruction

  case class Block(index: Int, label: Label, instructions: List[Instruction]) {
    def <:>(instr: Instruction) = Block(index, label, instructions :+ instr)
    def <:>(is: List[Instruction]) = Block(index, label, instructions ++ is)
    def <:>(that: Block) = Code(List(this, that), Nil)
  }

  case class Code(blocks: List[Block], current: List[Instruction]){
    def <:>(instr: Instruction) = Code(blocks, current :+ instr)
    def <:>(is: List[Instruction]) = Code(blocks, current ++ is)

    // def <:>(next: Block) = Code(merge :+ next, Nil)
    // def <:>(other: Code) = Code(merge ++ other.blocks, other.current)
    //
    // def merge() : List[Block] = if(blocks.isEmpty){
    //   List(Block.create(new Label("temp"))) //TODO find correct label to apply
    // } else {
    //   blocks.dropRight(1) :+ (blocks.last <:> current)
    // }
  }

  object Code {
    def empty: Code = new Code(Nil, Nil)
    def first(block: Block) = new Code(List(block), Nil)
  }

  //case object NoCode extends Code

  //Boolean operations
  case object And extends Instruction
  case object Or extends Instruction
  case object Not extends Instruction

  case object Neq extends Instruction
  case object Eq extends Instruction
  case object Lt extends Instruction
  case object Gt extends Instruction
  case object Leq extends Instruction
  case object Geq extends Instruction
  case object Nop extends Instruction
  case object Plus extends Instruction
  case object Minus extends Instruction
  case object Mul extends Instruction
  case object Div extends Instruction

  abstract class Literal extends Instruction
  case class BooleanLiteral(b: Boolean) extends Literal
  case class Const(n: BigInt) extends Literal
  case object UnitLiteral extends Literal

  class Value(val v: Either[Local, Literal])
  object Value {
    def apply(local: Local): Value = new Value(Left(local))
    def apply(literal: Literal): Value = new Value(Right(literal))
  }

  case class BinaryOp(op: Instruction, result: Local, lhs: Value, rhs: Value) extends Instruction
  case class UnaryOp(op: Instruction, result: Local, operand: Local) extends Instruction

  case class Assign(result: Local, from: Value) extends Instruction
  case class Variable(local: Local) extends Instruction
  //Terminator instructions
  //case class Ret()
  case class Branch(condition: Value, ifTrue: Label, ifFalse: Label) extends Instruction
  case class Jump(destination: Label) extends Instruction
  case class Return(result : Either[Local, Instruction]) extends Instruction
  case class Phi(res: Local, candidates: List[(Local, Label)]) extends Instruction

  case class MallocFunction(size: Int) extends Instruction
  case class Call(res: Local, function: Label) extends Instruction
}

class Label (val label: String){
  override def toString: String = s"%$label"
  def printLabel: String = s"$label:"
  def dot(s: String): Label = {
    new Label(label + "." + s)
  }
}

class Local (val name: String){
  override def toString: String = s"%$name"
  def dot(s: String): Local = {
    new Local(name + "." + s)
  }
}
