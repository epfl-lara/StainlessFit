package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ListBuffer

object ModulePrinter {


  private implicit def s2d(s: String) = Raw(s)

  def apply(mod: Module) = printModule(mod).print

  private def printModule(module: Module): Document = {
      var toPrint = new ListBuffer[Document]()

      if(!module.functions.isEmpty)
        toPrint += Stacked(module.functions.toList.map(_.print()), true)

      toPrint += Stacked("; Main function",
        Stacked(
          "define i32 @main(i32 %arg, i8** %arg1){",
            Indented(Stacked(module.blocks.toList.sortBy(_.index) map printBlock)),
            //Indented(s"ret i32 0"),
          "}"
        ))

        Stacked(toPrint.toList, emptyLines = true)
  }

  // private def printCode(code: Code): List[Document] = {
  //   code.merge.map(b => printBlock(b))
  // }

  private def printBlock(block: Block): Document = {
    Stacked(
      block.label.printLabel,
      Indented(Stacked(block.instructions map printInstr))
    )
  }

  private def printInstr(instr: Instruction): Document = {
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
      case Branch(condition, trueLocal, falseLocal) => Raw(s"br $condition, $trueLocal, $falseLocal")
      case Phi(res, choices) => Raw(s"$res = phi TYPE ") <:> Lined(choices.map(choice => s"[${choice._1}, ${choice._2}]"), ",")
      case Return(result) => result match {
        case Left(local) => Raw(s"ret i32 $local")
        case Right(instr) => Raw("ret i32 ") <:> printInstr(instr)
      }
      case other => Raw(s"PLACEHOLDER: $other")
    }
  }
}
