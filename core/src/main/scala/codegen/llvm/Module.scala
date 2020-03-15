package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ListBuffer


case class Module(name: String, main: Code, functions: List[Function]) {

  import java.io.{File, FileWriter}

  private implicit def s2d(s: String) = Raw(s)

  def printToFile(filename: String) = {
    val writer = new FileWriter(new File(filename))
    writer.write(printModule.print)
    writer.flush()
  }

  def printModule(): Document = {
      var toPrint = new ListBuffer[Document]()

      if(!functions.isEmpty)
        toPrint += Stacked(functions.map(_.print()), true)

      toPrint += Stacked("; Main function",
        Stacked(
          "define i32 @main(i32 %arg, i8** %arg1){",
            Indented(Stacked(printCode(main))),
            Indented(s"ret i32 0"),
          "}"
        ))

        Stacked(toPrint.toList, emptyLines = true)
  }

  def printCode(code: Code): List[Document] = {
    code.blocks.map(b => printBlock(b)) :+ printBlock(code.current)
  }

  def printBlock(block: Block): Document = {
    Stacked(
      s"${block.label}",
      Indented(Stacked(block.instructions map printInstr))
    )
  }

  def printInstr(instr: Instruction): Document = {
    instr match {
      case Primitive(op, args) => op match {
        case Or => Lined(args.map(printInstr(_)), " || ")
        case And => Lined(args.map(printInstr(_)), " && ")
        case Not => Lined(List("!", printInstr(args.head)))
      }
      case BooleanLiteral(b) => s"$b"
      case _ => Raw("PLACEHOLDER")
    }
  }
}

class TargetTriple {

}
