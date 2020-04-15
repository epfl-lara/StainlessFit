package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ListBuffer

object ModulePrinter {
  // 24:                                               ; preds = %10
  //   %25 = load i32*, i32** %6, align 8
  //   %26 = bitcast i32* %25 to i8*
  //   call void @free(i8* %26) #3
  //   %27 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0))
  //   store i32 256, i32* %8, align 4
  //   ret i32 0
  // }
  //
  // declare dso_local i32 @fprintf(%struct._IO_FILE*, i8*, ...) #2
  //
  // call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  private implicit def s2d(s: String) = Raw(s)

  def apply(mod: Module) = printModule(mod).print
  //def apply(fun: Function) = printFunction(fun).print
  // private val integerFormat = "%d\\00"
  // private val integerStr = "@.integer.str"
  // private val charFormat = "%c\\00"
  // private val charStr = "@.char.str"
  //
  // private def constStr(s) = i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0)
  //
  // private def format(format_: String) = "private unnamed_addr constant [3 x i8] c\"" + format_ + "\", align 1"
  //
  // private def callPrintf(toPrint: Either[(Value. Type), Char]) = {
  //   val (printArg, str) = toPrint match {
  //     case Left((value, tpe)) => (printType(tpe) <:> " " <:> printValue(value), integerStr)
  //     case Right(c) => (c, charStr)
  //   }
  //
  //   Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* $str, i64 0, i64 0))"
  // }

  private val openGlobal = "@.open"
  private val open = "private unnamed_addr constant [2 x i8] c\"(\\00\", align 1"

  private val closeGlobal = "@.close"
  private val close = "private unnamed_addr constant [2 x i8] c\")\\00\", align 1"

  private val commaGlobal = "@.comma"
  private val comma = "private unnamed_addr constant [3 x i8] c\", \\00\", align 1"

  private val integerGlobal = "@.integer"
  private val integer = "private unnamed_addr constant [3 x i8] c\"%d\\00\", align 1"

  private val trueGlobal = "@.true"
  private val true_ = "private unnamed_addr constant [6 x i8] c\"true\\00\\00\", align 1"

  private val falseGlobal = "@.false"
  private val false_ = "private unnamed_addr constant [6 x i8] c\"false\\00\", align 1"

  def printChar(c: String) = {
    val (global, size) = c match {
      case "(" => (openGlobal, 2)
      case ")" => (closeGlobal, 2)
      case "," => (commaGlobal, 3)
    }
    Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([$size x i8], [$size x i8]* $global, i64 0, i64 0))")
  }

  private def printModule(module: Module): Document = {
      var toPrint = new ListBuffer[Document]()

      toPrint += Raw(s"$openGlobal = $open")
      toPrint += Raw(s"$closeGlobal = $close")
      toPrint += Raw(s"$commaGlobal = $comma")
      toPrint += Raw(s"$integerGlobal = $integer")
      toPrint += Raw(s"$trueGlobal = $true_")
      toPrint += Raw(s"$falseGlobal = $false_")
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
      Lined(List(Raw(s"define "), printType(returnType), Raw(s" ${name}("), paramList, ") {")),
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

      case Printf(value, tpe) => {
        Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* $integerGlobal, i64 0, i64 0), ") <:> printType(tpe) <:> " " <:>
        printValue(value) <:>
        Raw(")")
      }

      case PrintOpen => printChar("(")
      case PrintClose => printChar(")")
      case PrintComma => printChar(",")

      case PrintBool(cond, local) => {
        Stacked(
          Raw(s"$local.select = select i1 $cond, [6 x i8]* $trueGlobal, [6 x i8]* $falseGlobal"),
          Raw(s"$local.string = getelementptr [6 x i8], [6 x i8]* $local.select, i64 0, i64 0"),
          Raw(s"call i32 (i8*, ...) @printf(i8* $local.string)")
        )
      }

      case Malloc(res, t1, t2, t3, tpe) => {
        Stacked(
          Raw(s"$t1 = getelementptr ") <:> printInMemoryType(tpe, true) <:> ", " <:> printType(tpe) <:> Raw(" null, i32 1"),
          Raw(s"$t2 = ptrtoint ") <:> printType(tpe) <:> Raw(s" $t1 to i64"),
          Raw(s"$t3 = call i8* @malloc(i64 $t2)"),
          Raw(s"$res = bitcast i8* $t3 to ") <:> printType(tpe)
        )
      }

      case GepToFirst(result, tpe, pair) => {
        Raw(s"$result = getelementptr ") <:> printInMemoryType(tpe, true) <:> Raw(", ") <:> printType(tpe) <:> Raw(s" $pair, i32 0, i32 0")
      }

      case GepToSecond(result, tpe, pair) => {
        Raw(s"$result = getelementptr ") <:> printInMemoryType(tpe, true) <:> Raw(", ") <:> printType(tpe) <:> Raw(s" $pair, i32 0, i32 1")
      }

      case Store(value, tpe, ptr) =>
        Lined(List(
          "store",
          printInMemoryType(tpe, true),
          printValue(value),
          ",",
          printType(tpe),
          s"$ptr"
        ), " ")

      case Load(result, tpe, ptr) => Lined(List(
        s"$result = load",
        printInMemoryType(tpe, true),
        ",",
        printType(tpe),
        s"$ptr"
      ), " ")

      case other => Raw(s"PLACEHOLDER: $other")
    }
  }

  private def printValue(value: Value): Document = value.v match {
    case Left(local) => s"$local"
    case Right(literal) => literal match {
      case UnitLiteral => "0"
      case BooleanLiteral(b) => s"$b"
      case Nat(n) => s"$n"
      case PairLiteral(first, second) => ???
    }
    case other => Raw(s"PLACEHOLDER: $other")
  }

  private def printType(tpe: Type)(implicit m: Module): Document = tpe match {
    case FunctionReturnType(funName) => s"${getFunction(funName).returnType}"
    case PointerType(tpe) => printType(tpe) <:> "*"
    case PairType(first, second) => Raw("{") <:> printType(first) <:> Raw(", ") <:> printType(second) <:> Raw("}")
    case _ => s"$tpe"
  }

  private def printInMemoryType(tpe: Type, topLevel: Boolean)(implicit m: Module): Document = tpe match {
    case PointerType(pointedType) => if(topLevel) printType(pointedType) else printType(tpe)
    case _ => printType(tpe)
  }

  private def getFunction(funName: Global)(implicit m: Module): Function = {
    m.functions.filter(fun => fun.name == funName).head
  }
}
