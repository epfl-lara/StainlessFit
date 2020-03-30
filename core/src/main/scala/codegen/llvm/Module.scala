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
    code.merge.map(b => printBlock(b))
  }

  def printBlock(block: Block): Document = {
    Stacked(
      s"${block.label}",
      Indented(Stacked(block.instructions map printInstr))
    )
  }

  def printInstr(instr: Instruction): Document = {
    instr match {
      // case Primitive(op, args) => op match {
      //   case Or => Lined(args.map(printInstr(_)), " || ")
      //   case And => Lined(args.map(printInstr(_)), " && ")
      //   case Not => Lined(List("!", printInstr(args.head)))
      // }

      // case BinaryOp(op, res, lhs, rhs) => op match {
      //   case And => Lined(List(printInstr(res), " = ", printInstr(lhs), " && ", printInstr(rhs)))
      //   case Or => Lined(List(printInstr(res), " = ", printInstr(lhs), " || ", printInstr(rhs)))
      // }
      // case UnaryOp(op, res, operand) => op match {
      //   case Not => Lined(List(printInstr(res), " = !", printInstr(operand)))
      // }
      // case Assigne(res, from) => Lined(List(printInstr(res), " = ", printInstr(from)))

      case BinaryOp(op, res, lhs, rhs) => op match {
        case And => Raw(s"$res = and $lhs, $rhs")
        case Or => Raw(s"$res = or $lhs, $rhs")
      }
      case UnaryOp(op, res, operand) => op match {
        case Not => Raw(s"$res = fneg $operand")
      }

      case Variable(local) => Raw(s"$local")
      case Assign(res, from) =>// Raw(s"$res = $from")
      Lined(List(s"$res = ", printInstr(from)))

      case BooleanLiteral(b) => s"$b"
      case _ => Raw("PLACEHOLDER")
    }
  }
}

class TargetTriple {
  //TODO
}
