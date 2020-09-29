/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package extraction

import util.RunContext
import util.Utils._
import trees._
import trees.TreeBuilders._
import parser.FitParser

class DefFunctionElimination(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (t.preMap(e => e match {
    case DefFunction(f, args, optRet, optMeasure, body, rest) =>
      if (f.isFreeIn(body) && optMeasure.isEmpty) {
        rc.reporter.fatalError(s"Recursive function $f needs a decreases clause.")
      }
      (optMeasure, optRet) match {
        case (Some(_), None) =>
          rc.reporter.fatalError(s"Recursive function $f needs a return type.")
        case (None, None) =>
          val fun = Abstractions(args, body)
          Some(LetIn(None, fun, Bind(f, rest)))
        case (None, Some(ty)) =>
          val fun = Abstractions(args, body)
          val funType = ForallQuantifiers(args, ty)
          Some(LetIn(Some(funType), fun, Bind(f, rest)))
        case (Some(measure), Some(ty)) =>
          val n = Identifier.fresh("n")

          val refinedArgs = mapFirst(args.reverse, { (arg: DefArgument) => arg match {
            case ForallArgument(id, ty) =>
              Some(ForallArgument(id, RefinementType(ty, Bind(id, Primitive(Leq, List(measure, Var(n)))))))
            case TypedArgument(id, ty) =>
              Some(TypedArgument(id, RefinementType(ty, Bind(id, Primitive(Leq, List(measure, Var(n)))))))
            case _ =>
              None
          }}).getOrElse {
            throw new java.lang.Exception(s"Recursive function $f with arguments: $args must have at least one (term) argument with a type")
          }.reverse

          val fun = Abstractions(refinedArgs, body)
          val funType = ForallQuantifiers(refinedArgs, ty)

          val fix = Fix(Some(Bind(n, funType)), Bind(n, Bind(f, fun)))

          val instBody = Applications(
            ErasableApp(Var(f), Primitive(Plus, List(measure, NatLiteral(1)))),
            args.map(_.toAppArgument())
          )
          val instFun = Abstractions(args, instBody)
          Some(LetIn(None, fix, Bind(f,
            LetIn(None, instFun, Bind(f,
              rest)
            )
          )))
      }
    case _ => None

  }), ())
}
