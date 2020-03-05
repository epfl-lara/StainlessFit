package stainlessfit
package core
package codegen.llvm

import trees.Identifier

object IR {

  abstract class Instruction

  case class Block(name: Identifier, instructions: List[Instruction]){
    def <:>(instr: Instruction) = Block(name, instructions :+ instr)
    def <:>(is: List[Instruction]) = Block(name, instructions ++ is)
  }

  case class Code(blocks: List[Block], current: Block){
    def <:>(instr: Instruction) = Code(blocks, current <:> instr)
    def <:>(is: List[Instruction]) = Code(blocks, current <:> is)

    def <:>(next: Block) = Code(blocks :+ current, next)
    def <:>(other: Code) = Code(blocks ++ (current +: other.blocks), other.current)
  }
}
