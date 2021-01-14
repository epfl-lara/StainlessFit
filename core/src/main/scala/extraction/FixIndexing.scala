/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package extraction

import util.RunContext
import trees._
import parser.FitParser

class FixIndexing(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = {
    (t.replace((e: Tree) => e match {
      case Fix(Some(Bind(n1, funType)), Bind(n2, Bind(f, body))) =>
        assert(n1 == n2)
        Some(Right(
          Fix(Some(Bind(n1, transform(funType)._1)), Bind(n2, Bind(f,
            transform(body.replace(f,
              ErasableApp(Var(f), Primitive(Minus, List(Var(n1), NatLiteral(1))))
            ))._1
          )))
        ))
      case _ =>
        None
    }).toOption.get, ())
  }
}
