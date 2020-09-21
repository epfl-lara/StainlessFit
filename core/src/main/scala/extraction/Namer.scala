/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package extraction

import util.RunContext
import trees._
import parser.FitParser
import typechecker.SDepSugar._

import scala.collection.mutable. { Map => MutableMap }

class Namer(implicit val rc: RunContext) extends Phase[Unit] {
  val builtInMap = (BuiltInIdentifiers.builtInIdentifiers ++ BuiltInIdentifiers.builtInTypeIdentifiers)
    .map(id => Identifier(0, id) -> Identifier(0, id)).toMap

  def transform(t: Tree): (Tree, Unit) = (namer(t), ())

  def namer(t: Tree): Tree = {
    val m = MutableMap(builtInMap.toSeq: _*)
    t.postMap(
      (t: Tree) => t match {
        case Bind(id, body) =>
          val freshId = id.freshen()
          val oldId = m.get(id)
          m(id) = freshId
          (res: Tree) => res match {
            case Bind(_, resBody) =>
              if (oldId.isEmpty) m.remove(id)
              else m(id) = oldId.get
              Bind(freshId, resBody)
            case _ => res
          }

        case Var(id) =>
          if (m.contains(id)) _ => Var(m(id))
          else rc.reporter.fatalError(
            s"Error in name resolution: undefined variable ${id.asString} at position ${t.pos}"
          )

        case _ => res => res
      }
    )
  }
}
