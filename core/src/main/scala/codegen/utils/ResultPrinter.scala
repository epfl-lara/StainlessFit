package stainlessfit
package core
package codegen.utils

import core.codegen.llvm.IR.{UnitType => IRUnitType, NatType => IRNatType, _}
import core.util.RunContext

object ResultPrinter {

  def apply(result: Local, tpe: Type, lh: LocalHandler, rc: RunContext): List[Instruction] = {

    def customPrint(toPrint: Local, tpe: Type, parentheses: Boolean): List[Instruction] = tpe match {
      case PairType(firstType, secondType) => {

        val (firstLocal, secondLocal) = (lh.dot(toPrint, "first"), lh.dot(toPrint, "second"))

        val (firstPtr, secondPtr) = (lh.dot(firstLocal, "gep"), lh.dot(secondLocal, "gep"))

        val prep = List(
          GepToFirst(firstPtr, tpe, toPrint),
          Load(firstLocal, firstType, firstPtr),
          GepToSecond(secondPtr, tpe, toPrint),
          Load(secondLocal, secondType, secondPtr)
        )

        val printFirst = customPrint(firstLocal, firstType, true)
        val printSecond = customPrint(secondLocal, secondType, false)

        val pair = printFirst ++ List(PrintComma) ++ printSecond
        val (open, close) = if(parentheses) (List(PrintOpen), List(PrintClose)) else (Nil, Nil)
        open ++ prep ++ pair ++ close
      }

      case BooleanType | IRUnitType => List(PrintBool(toPrint))

      case IRNatType => List(PrintNat(Value(toPrint)))

      case other => rc.reporter.fatalError(s"Pretty printing not implemented for $other yet")
      //TODO add case for Left and Right type
    }

    customPrint(result, tpe, true)
  }
}
