package stainlessfit
package core
package codegen.llvm

import core.util.RunContext

import core.codegen.llvm.IR._
import core.codegen.utils._

import scala.language.implicitConversions
import scala.collection.mutable.ListBuffer

object ModulePrinter {
   implicit def s2d(s: String) = Raw(s)

   val openGlobal = "@.open"
   val open = " unnamed_addr constant [2 x i8] c\"(\\00\", align 1"

   val closeGlobal = "@.close"
   val close = " unnamed_addr constant [2 x i8] c\")\\00\", align 1"

   val commaGlobal = "@.comma"
   val comma = " unnamed_addr constant [3 x i8] c\", \\00\", align 1"

   val natGlobal = "@.nat"
   val nat = " unnamed_addr constant [3 x i8] c\"%d\\00\", align 1"

   val trueGlobal = "@.true"
   val true_ = " unnamed_addr constant [6 x i8] c\"true\\00\\00\", align 1"

   val falseGlobal = "@.false"
   val false_ = " unnamed_addr constant [6 x i8] c\"false\\00\", align 1"

   val leftGlobal = "@.left"
   val left = " unnamed_addr constant [6 x i8] c\"left\\00\\00\", align 1"

   val rightGlobal = "@.right"
   val right = " unnamed_addr constant [6 x i8] c\"right\\00\", align 1"

  def printChar(c: String) = {
    val (global, size) = c match {
      case "(" => (openGlobal, 2)
      case ")" => (closeGlobal, 2)
      case "," => (commaGlobal, 3)
    }
    Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([$size x i8], [$size x i8]* $global, i64 0, i64 0))")
  }

  def run(mod: Module)(implicit rc: RunContext) = {

     def printModule: Document = {
        var toPrint = new ListBuffer[Document]()

        toPrint += Stacked(
          Raw(s"$openGlobal = $open"),
          Raw(s"$closeGlobal = $close"),
          Raw(s"$commaGlobal = $comma"),
          Raw(s"$natGlobal = $nat"),
          Raw(s"$trueGlobal = $true_"),
          Raw(s"$falseGlobal = $false_"),
          Raw(s"$leftGlobal = $left"),
          Raw(s"$rightGlobal = $right")
        )

        toPrint += Raw("declare dso_local noalias i8* @malloc(i64) local_unnamed_addr")
        toPrint += Raw("declare dso_local i32 @printf(i8*, ...)")

        if(!mod.functions.isEmpty)
          toPrint += Stacked(
              mod.functions.toList.map(f => printFunction(f)),
              true)

        toPrint += printFunction(mod.main)

        Stacked(toPrint.toList, emptyLines = true)
    }

     def printFunction(fun: Function): Document = {
      val Function(returnType, name, params, blocks) = fun
      val paramList = Lined(params.map(param => printType(param.tpe) <:> s" ${param.local}"), ", ")
      Stacked(
        Lined(List(Raw(s"define "), printType(returnType), Raw(s" $name("), paramList, ") {")),
        Indented(Stacked(blocks.toList.sortBy(_.index) map printBlock, true)),
        "}"
      )
    }

     def printBlock(block: Block): Document = {
      Stacked(
        block.label.printLabel,
        Indented(Stacked(block.instructions map printInstr))
      )
    }

     def printInstr(instr: Instruction): Document = {
      instr match {

        case BinaryOp(op, res, lhs, rhs) => {
          val tpe = op match {
            case compOp: ComparisonOperator =>  NatType
            case _ => op.returnType
          }

          Lined(List(s"$res = $op ", printType(tpe), " ", printValue(lhs), ", ", printValue(rhs)))
        }

        case UnaryOp(op, res, operand) => op match {
          case Not => Raw(s"$res = $op ${op.returnType} $operand")
        }

        case Variable(local) => Raw(s"$local")

        case Assign(res, tpe, from) => extractNestedType(tpe) match {

          case PairType(t1, t2) => printInstr(GepToIdx(res, tpe, from, None))
          case EitherType(t1, t2) => printInstr(GepToIdx(res, tpe, from, None))

          case NatType => Lined(List(s"$res = add", printType(tpe), "0,", printValue(from)), " ")
          case _ =>       Lined(List(s"$res = or", printType(tpe), "0,", printValue(from)), " ")
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

          Raw(s"$result = call ") <:> printType(returnType) <:> (s" $funName(") <:>
          Lined(valueTypes.zip(values).map{case (tpe, value) => printType(tpe) <:> " " <:> printValue(value)}, ", ") <:>
          Raw(")")
        }

        case PrintNat(value) => {
          Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* $natGlobal, i64 0, i64 0), i32 ") <:>
          printValue(value) <:>
          Raw(")")
        }

        case PrintOpen => printChar("(")
        case PrintClose => printChar(")")
        case PrintComma => printChar(",")

        case PrintBool(cond) => {
          Stacked(
            Raw(s"$cond.selectStr = select i1 $cond, [6 x i8]* $trueGlobal, [6 x i8]* $falseGlobal"),
            Raw(s"$cond.string = getelementptr [6 x i8], [6 x i8]* $cond.selectStr, i64 0, i64 0"),
            Raw(s"call i32 (i8*, ...) @printf(i8* $cond.string)")
          )
        }

        case PrintResult(result, printType, lh) => Stacked(
          ResultPrinter(result, extractNestedType(printType), lh, rc) map printInstr
        )

        case Malloc(res, t1, t2, t3, tpe) => {
          val typeString = printType(tpe, false).print
          Stacked(
            Raw(s"$t3 = call i8* @malloc(i64 ptrtoint ($typeString* getelementptr ($typeString, $typeString* null, i32 1) to i64))"),
            Raw(s"$res = bitcast i8* $t3 to $typeString*")
          )
        }

        case GepToIdx(result, tpe, ptr, idx) => {
          Lined(List(
            Raw(s"$result = getelementptr"),
            printType(tpe, false) <:> Raw(","),
            printType(tpe),
            printValue(ptr) <:> Raw(","),
            Raw("i32 0"),
            idx.fold(Raw(""))(n => s", i32 $n")
          ), " ")
        }

        case Store(value, tpe, ptr) => Lined(List(
          "store", printType(tpe), printValue(value), ",", printType(tpe) <:> "*", s"$ptr"), " ")

        case Load(result, tpe, ptr) => Lined(List(
          s"$result = load", printType(tpe), ",", printType(tpe) <:> "*", s"$ptr"), " ")

        case NoOp => ""

        case other => Raw(s"PLACEHOLDER: $other")
      }
    }

     def printValue(value: Value): Document = value.v match {
      case Left(local) => s"$local"
      case Right(literal) => literal match {
        case UnitLiteral => "0"
        case BooleanLiteral(b) => s"$b"
        case Nat(n) => s"$n"
      }
      case other => Raw(s"PLACEHOLDER: $other")
    }

     def getFunction(funName: Global): Function = {
      mod.functions.filter(fun => fun.name == funName).head
    }


    def printType(tpe: Type, ptr: Boolean = true): Document = extractNestedType(tpe) match {
      case PairType(first, second) =>
        Raw("{") <:> printType(first) <:> Raw(", ") <:> printType(second) <:> Raw("}") <:> (if(ptr) "*" else "")
      case NatType => "i32"
      case BooleanType | UnitType => "i1"
      case EitherType(left, right) => //{i1, left, right} TODO store allocate only {i1, max(left, right)}
        Raw("{i1, ") <:> printType(left) <:> Raw(", ") <:> printType(right) <:> Raw("}") <:> (if(ptr) "*" else "")
      case LeftType(either) => Raw("{i1, ") <:> printType(either) <:> Raw("}") <:> (if(ptr) "*" else "")
      case RightType(either) => Raw("{i1, ") <:> printType(either) <:> Raw("}") <:> (if(ptr) "*" else "")

      case other=> Raw(s"PLACEHOLDER: $other")
    }

    def extractNestedType(tpe: Type): Type = tpe match {
      case FunctionReturnType(funName) => getFunction(funName).returnType
      case FirstType(nested) => extractNestedType(nested) match {
        case PairType(first, _) => first
        case other => rc.reporter.fatalError(s"Cannot apply First to $other")
      }

      case SecondType(nested) => extractNestedType(nested) match {
        case PairType(_, second) => second
        case other => rc.reporter.fatalError(s"Cannot apply Second to $other")
      }

      case LeftType(nested) => LeftType(extractNestedType(nested))
      case RightType(nested) => RightType(extractNestedType(nested))
      // case RightType(nested) => extractNestedType(nested) match {
      //   case EitherType(_, right) => right
      //   case other => rc.reporter.fatalError(s"Cannot apply right to $other")
      // }

      case other => other
    }

    printModule.print
  }
}
