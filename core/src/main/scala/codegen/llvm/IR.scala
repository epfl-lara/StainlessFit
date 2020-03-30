package stainlessfit
package core
package codegen.llvm

object IR {

  abstract class Instruction

  case class Block(label: Label, instructions: List[Instruction]){
    def <:>(instr: Instruction) = Block(label, instructions :+ instr)
    def <:>(is: List[Instruction]) = Block(label, instructions ++ is)
    def <:>(that: Block) = Code(List(this, that), Nil)
  }

  object Block {
    def create(label: Label): Block = new Block(label, Nil)
  }

  case class Code(blocks: List[Block], current: List[Instruction]){
    def <:>(instr: Instruction) = Code(blocks, current :+ instr)
    def <:>(is: List[Instruction]) = Code(blocks, current ++ is)

    def <:>(next: Block) = Code(merge :+ next, Nil)
    def <:>(other: Code) = Code(merge ++ other.blocks, other.current)

    def merge() : List[Block] = if(blocks.isEmpty){
      List(Block.create(new Label("temp"))) //TODO find correct label to apply
    } else {
      blocks.dropRight(1) :+ (blocks.last <:> current)
    }
  }

  object Code {
    def empty: Code = new Code(Nil, Nil)
    def first(block: Block) = new Code(List(block), Nil)
  }

  case class Const(n: Int) extends Instruction

  //Boolean operations
  // case class And(res: Local, left: Local, right: Local) extends Instruction
  // case class Or(res: Local, left: Local, right: Local) extends Instruction
  // case class Not(res: Local, left: Local, right: Local) extends Instruction
  case object And extends Instruction
  case object Or extends Instruction
  case object Not extends Instruction

  case class BooleanLiteral(b: Boolean) extends Instruction
  case class BinaryOp(op: Instruction, result: Local, lhs: Local, rhs: Local) extends Instruction
  case class UnaryOp(op: Instruction, result: Local, operand: Local) extends Instruction

  case class Assign(result: Local, from: Instruction) extends Instruction
  case class Variable(local: Local) extends Instruction
  //Terminator instructions
  //case class Ret()
  case class Branch(condition: Local, ifTrue: Label, ifFalse: Label) extends Instruction
  case class Jump(destination: Label) extends Instruction

  case class Phi(res: Local, candidates: List[(Local, Label)]) extends Instruction

  case class MallocFunction(size: Int) extends Instruction
  case class Call(res: Local, function: Label) extends Instruction
}

class Label (val label: String){
  override def toString: String = s"$label:"
}

class Local (val name: String) {
  override def toString: String = s"%$name"
}
