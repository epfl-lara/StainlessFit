package fit
package core
package extraction

import codegen.CodeGen
import parser.FitParser
import trees._
import TreeBuilders._
import util.RunContext

class DefFunctionLLVMConversion(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (DefFunctionLLVMConversion.convert(t), ())
}

object DefFunctionLLVMConversion {

  def convert(t: Tree)(implicit rc: RunContext): Tree = (t.postMap(_ => e => e match {
    case defFun @ DefFunction(_, _, _, _, _, _) => convertDefFun(defFun)
    case _ => e
  }))

  def convertDefFun(defFun: Tree)(implicit rc: RunContext): Tree = {

    val DefFunction(f, args, optReturnType, optMeasure, body, rest) = defFun

    val value = Abstractions(args, body)

    val optFunType = optReturnType match {
      case Some(ty) => {
        Some(ForallQuantifiers(args, ty))
      }
      case None => None
      case other => rc.reporter.fatalError(s"Unreachable code (DefFunctionLLVMConversion)")
    }

    LetIn(optFunType, value, Bind(f, rest))
  }
}
