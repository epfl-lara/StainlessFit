package fit
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
   val open = "unnamed_addr constant [2 x i8] c\"(\\00\", align 1"

   val closeGlobal = "@.close"
   val close = "unnamed_addr constant [2 x i8] c\")\\00\", align 1"

   val commaGlobal = "@.comma"
   val comma = "unnamed_addr constant [3 x i8] c\", \\00\", align 1"

   val natGlobal = "@.nat"
   val nat = "unnamed_addr constant [3 x i8] c\"%d\\00\", align 1"

   val trueGlobal = "@.true"
   val true_ = "unnamed_addr constant [6 x i8] c\"true\\00\\00\", align 1"

   val falseGlobal = "@.false"
   val false_ = "unnamed_addr constant [6 x i8] c\"false\\00\", align 1"

   val leftGlobal = "@.left"
   val left = " unnamed_addr constant [7 x i8] c\"left \\00\\00\", align 1"

   val rightGlobal = "@.right"
   val right = "unnamed_addr constant [7 x i8] c\"right \\00\", align 1"

  def printChar(c: String) = {
    val (global, size) = c match {
      case "(" => (openGlobal, 2)
      case ")" => (closeGlobal, 2)
      case "," => (commaGlobal, 3)
      case "left" => (leftGlobal, 7)
      case "right" => (rightGlobal, 7)
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
        toPrint += Raw("declare dso_local void @exit(i32)")

        if(!mod.lambdas.isEmpty)
          toPrint += Stacked(
              mod.lambdas.reverse.toList.map(l => printLambda(l)),
              true)

        toPrint += printMain(mod.main)

        Stacked(toPrint.toList, emptyLines = true)
    }

    def printMain(main: Function): Document = {
      Stacked(
        Raw(s"define i32 @main() {"),
        Indented(Stacked(main.blocks.toList.sortBy(_.index) map printBlock, true)),
        "}"
      )
    }

    def printLambda(fun: Function): Document = {

      val paramList = Lined(fun.params.map(param => printType(param.tpe) <:> s" ${param.local}"), ", ")

      Stacked(
        Lined(List(Raw(s"define "), printType(fun.returnType), Raw(s" ${fun.name}("), paramList, s") {")),
        Indented(Stacked(fun.blocks.toList.sortBy(_.index) map printBlock, true)),
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

        case Variable(local) => Raw(s"$local")

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

        case Phi(res, tpe, choices) =>{
          Raw(s"$res = phi ") <:> printType(tpe) <:> " " <:>
           Lined(choices.map(choice => s"[${choice._1}, ${choice._2}]"), ", ")
        }

        case Assign(res, tpe, from) => extractNestedType(tpe) match {

          case PairType(t1, t2) => printInstr(GepToIdx(res, tpe, from, None))
          case EitherType(t1, t2) => printInstr(GepToIdx(res, tpe, from, None))
          case LambdaType(argType, retType) => printInstr(GepToIdx(res, tpe, from, None))

          case NatType => Lined(List(s"$res = add", printType(tpe), "0,", printValue(from)), " ")
          case _ =>       Lined(List(s"$res = or", printType(tpe), "0,", printValue(from)), " ")
        }

        case Call(result, returnType, funName, values, valueTypes, env) => {
          val valueList = valueTypes.zip(values).map{case (tpe, value) => printType(tpe) <:> " " <:> printValue(value)}

          Raw(s"$result = call ") <:> printType(returnType) <:> Raw(s" $funName(") <:>
          Lined(valueList :+ "i8* ", ", ") <:>
          printValue(env) <:> Raw(")\n")
        }

        //Terminator instructions
        case Branch(condition, trueLocal, falseLocal) =>
          Lined(List(s"br i1 ", printValue(condition), s", label $trueLocal, label $falseLocal"))

        case Jump(dest) => Raw(s"br label $dest")

        case Return(result, tpe) =>
          Lined(List(Raw("ret"), printType(tpe), printValue(result)), " ")

        case Exit => Raw("call void @exit(i32 1)")

        //Memory instructions
        case Load(result, tpe, ptr) => Lined(
          List(s"$result = load", printType(tpe) <:> ",", printType(tpe) <:> "*", s"$ptr"),
           " ") <:> Raw("\n")

        case Store(value, tpe, ptr) => Lined(
          List("store", printType(tpe), printValue(value) <:> ",", printType(tpe) <:> "*", s"$ptr"),
          " ") <:> Raw("\n")

        case GepToIdx(result, tpe, ptr, idx) => {
          Lined(List(
            Raw(s"$result = getelementptr"),
            printType(tpe, false) <:> Raw(","),
            printPointerType(tpe),
            printValue(ptr) <:> Raw(","),
            Raw("i32 0"),
            idx.fold(Raw(""))(n => s", i32 $n")
          ), " ")
        }

        case Malloc(res, temp, tpe) => {
          val typeString = printType(tpe, false).print
          Stacked(
            Raw(s"$temp = call i8* @malloc(i64 ptrtoint ($typeString* getelementptr ($typeString, $typeString* null, i32 1) to i64))"),
            Raw(s"$res = bitcast i8* $temp to $typeString*"),
            Raw("")
          )
        }

        case Bitcast(res, local, toType) =>
          Raw(s"$res = bitcast i8* $local to ") <:> printType(toType, false) <:> "*" <:> Raw("\n")

        //Pretty printing instructions
        case PrintNat(value) => {
         Raw(s"call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* $natGlobal, i64 0, i64 0), i32 ") <:>
         printValue(value) <:>
         Raw(")")
        }

        case PrintBool(cond) => {
         Stacked(
           Raw(s"$cond.selectStr = select i1 $cond, [6 x i8]* $trueGlobal, [6 x i8]* $falseGlobal"),
           Raw(s"$cond.string = getelementptr [6 x i8], [6 x i8]* $cond.selectStr, i64 0, i64 0"),
           Raw(s"call i32 (i8*, ...) @printf(i8* $cond.string)")
         )
        }

        case PrintOpen => printChar("(")
        case PrintClose => printChar(")")
        case PrintComma => printChar(",")
        case PrintLeft => printChar("left")
        case PrintRight => printChar("right")

        case PrintError(msg, errLocal) => {

          val error = "c\"" + msg + "\\00\""
          val errorSize = msg.size + 1
          Stacked(
            Raw(s"$errLocal.alloc = alloca [$errorSize x i8]"),
            Raw(s"store [$errorSize x i8] " + error + s", [$errorSize x i8]* $errLocal.alloc"),
            Raw(s"$errLocal = getelementptr [$errorSize x i8], [$errorSize x i8]* $errLocal.alloc, i32 0, i32 0"),
            Raw(s"call i32 (i8*, ...) @printf(i8* $errLocal)")
          )
        }

        case other => rc.reporter.fatalError("Unknown instruction during printing")
      }
    }

     def printValue(value: Value): Document = value.v match {
      case Left(name) => s"$name"
      case Right(literal) => literal match {
        case UnitLiteral => "0"
        case BooleanLiteral(b) => s"$b"
        case Nat(n) => s"$n"
        case NullLiteral => "null"

        case other => rc.reporter.fatalError("Unknown value during printing")
      }
    }

    def printType(tpe: Type, ptr: Boolean = true): Document = extractNestedType(tpe) match {
      case BooleanType | UnitType => "i1"

      case NatType => "i32"

      case PairType(first, second) =>
        Raw("{") <:> printType(first) <:> Raw(", ") <:> printType(second) <:> Raw("}") <:> (if(ptr) "*" else "")

      case EitherType(left, right) =>
        Raw("{i1, ") <:> printType(left) <:> Raw(", ") <:> printType(right) <:> Raw("}") <:> (if(ptr) "*" else "")

      case LeftType(either) => printType(either)
      case RightType(either) => printType(either)

      case LambdaType(argType, retType) =>
        Raw("{") <:> printType(FunctionType(argType, retType)) <:> Raw(", i8*}") <:> (if(ptr) "*" else "")

      case FunctionType(argType, resType) =>
        printType(resType) <:> Raw(" (") <:> printType(argType) <:> Raw(", i8*)*")

      case EnvironmentType(types) =>
        Raw("{") <:> Lined(types.map(t => printType(t)), ", ")<:> Raw("}") <:> (if(ptr) "*" else "")

      case RawEnvType => "i8*"

      case other => rc.reporter.fatalError("Unknown type during printing")
    }

    def printPointerType(tpe: Type): Document = tpe match {
      case NatType | BooleanType | UnitType => printType(tpe) <:> "*"
      case _ => printType(tpe)
    }

    def extractNestedType(tpe: Type): Type = tpe match {
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

      case other => other
    }

    printModule.print
  }
}
