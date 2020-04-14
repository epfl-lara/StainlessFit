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
  //def apply(fun: Function) = printFunction(fun).print
  private val format = "%d\\00"
  private val printfStr = "@.str = private unnamed_addr constant [3 x i8] c\"" + format + "\", align 1"

  private def printModule(module: Module): Document = {
      var toPrint = new ListBuffer[Document]()

      toPrint += Raw(printfStr)
      toPrint += Raw("declare dso_local noalias i8* @malloc(i64) local_unnamed_addr")
      toPrint += Raw("declare dso_local i32 @printf(i8*, ...)")

      if(!module.functions.isEmpty)
        toPrint += Stacked(
            module.functions.toList.map(f => printFunction(f)(module)),
            true)

      toPrint += printFunction(module.main)(module)

      Stacked(toPrint.toList, emptyLines = true)
  }

  private def printFunction(fun: Function)(implicit m: Module): Document = {
    val Function(returnType, name, params, blocks) = fun
    val paramList = Lined(params.map(param => s"${param.tpe} ${param.local}"), ", ")
    Stacked(
      Lined(List(s"define $returnType ${name}(", paramList, ") {")),
      Indented(Stacked(blocks.toList.sortBy(_.index) map printBlock, true)),
      "}"
    )
  }

  private def printBlock(block: Block)(implicit m: Module): Document = {
    Stacked(
      block.label.printLabel,
      Indented(Stacked(block.instructions map printInstr))
    )
  }

  private def printInstr(instr: Instruction)(implicit m: Module): Document = {
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

        Lined(List(s"$res = $op", printType(tpe), "0,", printValue(from)), " ")
      }

      case Branch(condition, trueLocal, falseLocal) =>
        Lined(List(s"br i1 ", printValue(condition), s", label $trueLocal, label $falseLocal"))

      case Jump(dest) => Raw(s"br label $dest")

      case Phi(res, tpe, choices) => Raw(s"$res = phi ") <:> printType(tpe) <:> " " <:>
        Lined(choices.map(choice => s"[${choice._1}, ${choice._2}]"), ", ")

      case Return(result, tpe) =>
        Lined(List(Raw("ret"), printType(tpe), printValue(result)), " ")

      //Todo void functions?
      case Call(result, funName, values) => {
        val f = getFunction(funName)
        val returnType = f.returnType
        val valueTypes = f.params.map(_.tpe)

        Raw(s"$result = call $returnType $funName(") <:>
        Lined(valueTypes.zip(values).map{case (tpe, value) => printType(tpe) <:> " " <:> printValue(value)}, ", ") <:>
        Raw(")")
      }

      case Printf(value, tpe) =>
        Raw("call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i64 0, i64 0), ") <:> printType(tpe) <:> " " <:>
        printValue(value) <:>
        Raw(")")

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

  private def printType(tpe: Type)(implicit m: Module): Document = tpe match {
    case FunctionReturnType(funName) => s"${getFunction(funName).returnType}"
    case _ => s"$tpe"
  }

  private def getFunction(funName: Global)(implicit m: Module): Function = {
    m.functions.filter(fun => fun.name == funName).head
  }
}
