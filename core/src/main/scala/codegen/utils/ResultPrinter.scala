package stainlessfit
package core
package codegen.utils

import codegen.llvm.IR.{UnitType => IRUnitType, NatType => IRNatType, _}
import codegen.llvm._
import codegen.CodeGen
import util.RunContext

class ResultPrinter(rc: RunContext) {

  def jumpTo(next: Option[Label]) = next.toList.map(label => Jump(label))

  def customPrint(block: Block, toPrint: Local, tpe: Type, flattenPairs: Boolean, next: Option[Label])
    (implicit lh: LocalHandler, f: Function): Block = tpe match {
    case BooleanType | IRUnitType => block <:> PrintBool(toPrint)

    case IRNatType => block <:> PrintNat(Value(toPrint))

    case PairType(firstType, secondType) => {

      val (firstLocal, secondLocal) = (lh.dot(toPrint, "first"), lh.dot(toPrint, "second"))
      val (firstPtr, secondPtr) = (lh.dot(firstLocal, "gep"), lh.dot(secondLocal, "gep"))
      val (open, close) = if(flattenPairs) (Nil, Nil) else (List(PrintOpen), List(PrintClose))

      val prepPair = List(
        GepToIdx(firstPtr, tpe, Value(toPrint), Some(0)),
        Load(firstLocal, firstType, firstPtr),
        GepToIdx(secondPtr, tpe, Value(toPrint), Some(1)),
        Load(secondLocal, secondType, secondPtr)
      )

      val firstPrinted = customPrint(block <:> prepPair <:> open, firstLocal, firstType, false, None)
      val secondPrinted = customPrint(firstPrinted <:> PrintComma, secondLocal, secondType, true, None)

      secondPrinted <:> close <:> jumpTo(next)
    }

    case eitherType @ EitherType(leftType, rightType) => {
      //Dynamically choose between Left and Right
      val leftBlockLabel = lh.dot(block.label, "left")
      val leftBlockStart = lh.newBlock(leftBlockLabel)
      val rightBlockLabel = lh.dot(block.label, "right")
      val rightBlockStart = lh.newBlock(rightBlockLabel)

      val helper = new CodeGen(rc)
      val choose = helper.cgEitherChoose(toPrint, tpe, leftBlockLabel, rightBlockLabel)
      f.add(block <:> choose)

      val afterPrinting = lh.dot(block.label, "keep.printing")

      //If the value is a LeftTree
      // val eitherLeftPtr = lh.dot(toPrint, "left.gep")
      // val leftLocal = lh.dot(toPrint, "left")
      // val prepLeft = List(
      //   GepToIdx(eitherLeftPtr, tpe, Value(toPrint), Some(1)),
      //   Load(leftLocal, leftType, eitherLeftPtr))
      val (leftLocal, prepLeft) = helper.getLeft(toPrint, eitherType)

      val leftBlock = leftBlockStart <:> prepLeft
      val leftPrinted = customPrint(leftBlock, leftLocal, LeftType(leftType), false, Some(afterPrinting))
      f.add(leftPrinted)

      //If the value is a RightTree
      // val eitherRightPtr = lh.dot(toPrint, "right.gep")
      // val rightLocal = lh.dot(toPrint, "right")
      // val prepRight = List(
      //   GepToIdx(eitherRightPtr, tpe, Value(toPrint), Some(2)),
      //   Load(rightLocal, rightType, eitherRightPtr))
      val (rightLocal, prepRight) = helper.getRight(toPrint, eitherType)

      val rightBlock = rightBlockStart <:> prepRight
      val rightPrinted = customPrint(rightBlock, rightLocal, RightType(rightType), false, Some(afterPrinting))
      f.add(rightPrinted)

      lh.newBlock(afterPrinting) <:> jumpTo(next)
    }

    case LeftType(innerType) => {
      val (open, close) = innerType match {
        case LeftType(_) | RightType(_) | EitherType(_, _) => (List(PrintOpen), List(PrintClose))
        case _ => (Nil, Nil)
      }

      val valuePrinted = customPrint(block <:> PrintLeft <:> open, toPrint, innerType, false, None)
      valuePrinted <:> close <:> jumpTo(next)
    }

    case RightType(innerType) => {
      val (open, close) = innerType match {
        case RightType(_) | LeftType(_) | EitherType(_, _) => (List(PrintOpen), List(PrintClose))
        case _ => (Nil, Nil)
      }

      val valuePrinted = customPrint(block <:> PrintRight <:> open, toPrint, innerType, false, None)
      valuePrinted <:> close <:> jumpTo(next)
    }

    case other => rc.reporter.fatalError(s"Pretty printing not implemented for $other yet")
  }
}
