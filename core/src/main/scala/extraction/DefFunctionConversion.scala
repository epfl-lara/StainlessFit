package stainlessfit
package core
package extraction

import codegen.CodeGen
import parser.FitParser
import trees._
import util.RunContext

class DefFunctionConvertion(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (DefFunctionConvertion.convert(t), ())
}

object DefFunctionConvertion {

  def convert(t: Tree)(implicit rc: RunContext): Tree = (t.replaceMany(e => e match {
    case defFun @ DefFunction(_, _, _, _, _) => Some(convertDefFun(defFun))
    case _ => None
  }))

  def convertDefFun(defFun: DefFunction)(implicit rc: RunContext) = {

    val DefFunction(args, optReturnType, optMeasure, bind, rest) = defFun
    //TODO shoudl work with 0 args too
    val TreeBuilders.Binds(ids, body) = bind
    val value = TreeBuilders.Abstractions(args, body) //nestLambdas(args, body)

    val optFunType = optReturnType match {
      case Some(TreeBuilders.Binds(_, ty)) => {
        Some(TreeBuilders.ForallQuantifiers(args, ty))
      }
      case None => None
      case other => rc.reporter.fatalError(s"Return type of DefFunction is $other")
    }

    LetIn(optFunType, value, rest)
  }
}
