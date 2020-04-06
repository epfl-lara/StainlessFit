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
  def apply(fun: Function) = printFunction(fun).print

  def printFunction(fun: Function): Document = {
    val Function(returnType, name, params, blocks) = fun
    val paramList = Lined(params.map(param => s"${param.tpe} ${param.local}"), ", ")
    Stacked(
      Lined(List(s"define $returnType ${name}(", paramList, ") {")),
      Indented(Stacked(blocks.toList.sortBy(_.index) map printBlock, true)),
      "}"
    )
  }

  private def printModule(module: Module): Document = {
      var toPrint = new ListBuffer[Document]()

      if(!module.functions.isEmpty)
        toPrint += Stacked(module.functions.toList map printFunction, true)

      toPrint += printFunction(module.main)

      Stacked(toPrint.toList, emptyLines = true)
  }

  private def printBlock(block: Block): Document = {
    Stacked(
      block.label.printLabel,
      Indented(Stacked(block.instructions map printInstr))
    )
  }

  private def printInstr(instr: Instruction): Document = {
    instr match {

      case BinaryOp(op, res, lhs, rhs) => {
        val tpe = op match {
          case compOp: ComparisonOperator =>  "i32"
          case _ => s"${op.returnType}"
        }

        Lined(List(s"$res = $op $tpe ", printValue(lhs), ", ", printValue(rhs)))
      }

      case UnaryOp(op, res, operand) => op match {
        case Not => Raw(s"$res = $op ${op.returnType} $operand")
      }

      case Variable(local) => Raw(s"$local")

      case Assign(res, tpe, from) => {
        val op = tpe match {
          case NatType => "add"
          case _ => "or"
        }

        Lined(List(s"$res = $op $tpe 0, ", printValue(from)))
      }

      case Branch(condition, trueLocal, falseLocal) =>
        Lined(List(s"br i1 ", printValue(condition), s", label $trueLocal, label $falseLocal"))

      case Jump(dest) => Raw(s"br label $dest")

      case Phi(res, tpe, choices) => Raw(s"$res = phi $tpe ") <:>
        Lined(choices.map(choice => s"[${choice._1}, ${choice._2}]"), ",") //TODO add type

      case Return(result, tpe) => result.v match {
        case Left(local) => Raw(s"ret $tpe $local")
        case Right(instr) => Raw(s"ret $tpe ") <:> printInstr(instr)
      }

      //Todo void functions?
      case Call(result, funName, args) =>
        Raw(s"$result = call RETURNTYPE $funName(") <:>
        Lined(args.map(arg => Raw(s"VALUETYPE ") <:> printValue(arg)), ", ") <:>
        Raw(")")
        //Lined(params.map(param => s"${param.tpe} ${param.local}"), ", ")
      case other => Raw(s"PLACEHOLDER: $other")
    }
  }

  private def printValue(value: Value): Document = value.v match {
    case Left(local) => s"$local"
    case Right(literal) => literal match {
      case UnitLiteral => "0"
      case BooleanLiteral(b) => s"$b"
      case Nat(n) => s"$n"
    }
    case other => Raw(s"PLACEHOLDER: $other")
  }
}
