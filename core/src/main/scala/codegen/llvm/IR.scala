package stainlessfit
package core
package codegen.llvm

object IR {

  abstract class Instruction

  case class Block(label: Label, instructions: List[Instruction]){
    def <:>(instr: Instruction) = Block(label, instructions :+ instr)
    def <:>(is: List[Instruction]) = Block(label, instructions ++ is)
  }

  case class Code(blocks: List[Block], current: Block){
    def <:>(instr: Instruction) = Code(blocks, current <:> instr)
    def <:>(is: List[Instruction]) = Code(blocks, current <:> is)

    def <:>(next: Block) = Code(blocks :+ current, next)
    def <:>(other: Code) = Code(blocks ++ (current +: other.blocks), other.current)
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
  case class Primitive(op: Instruction, args: List[Instruction]) extends Instruction


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
