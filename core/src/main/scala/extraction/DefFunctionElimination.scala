package stainlessfit
package core
package extraction

import util.RunContext
import util.Utils._
import trees._
import trees.TreeBuilders._
import parser.FitParser

class DefFunctionElimination(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (t.replaceMany(e => e match {
    case DefFunction(args, optRet, optMeasure, Binds(ids :+ f, body), Binds(ids2 :+ g, rest)) =>
      assert(ids2 == ids)
      assert(f == g)

      if (f.isFreeIn(body) && optMeasure.isEmpty) {
        rc.reporter.fatalError(s"Recursive function $f needs a decreases clause.")
      }
      (optMeasure, optRet) match {
        case (Some(_), None) =>
          rc.reporter.fatalError(s"Recursive function $f needs a return type.")
        case (None, None) =>
          val fun = Abstractions(args, body)
          Some(LetIn(None, fun, Bind(f, rest)))
        case (None, Some(Binds(ids3, ty))) =>
          assert(ids3 == ids)
          val fun = Abstractions(args, body)
          val funType = ForallQuantifiers(args, ty)
          Some(LetIn(Some(funType), fun, Bind(f, rest)))
        case (Some(Binds(ids4, measure)), Some(Binds(ids5, ty))) =>
          assert(ids4 == ids)
          assert(ids5 == ids)
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
            args.map(_.toAppArgument)
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
