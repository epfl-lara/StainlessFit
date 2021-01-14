/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package typechecker

import core.trees._

import util.RunContext
import util.Utils._

import Derivation._

trait MetaRules {

  implicit val rc: RunContext

  // This functions returns:
  // * `None` when `inst` is not a macro instantiation corresponding to `id`
  // * `Some(Left(error))` when it is, but there is an error
  // * `Some(Right(res))` when the macro instantiation is correct (and `res` is the result of the instantiation)
  def macroTypeInst(id: Identifier, tp: Tree, inst: Tree): Option[Either[String,Tree]] = inst match {
    case MacroTypeInst(Var(`id`), args) =>
      def loop(remBinders: Tree, remArgs: Seq[(Boolean, Tree)], acc: Map[Identifier, Tree])
        : Option[(Tree, Map[Identifier, Tree])] = {
        remBinders match {
          case Bind(x, body) =>
            remArgs match {
              case (isTerm, e) +: es if isTerm == x.isTermIdentifier =>
                loop(body, es, acc.updated(x, e))
              case _ =>
                None
            }
          case _ =>
            if (remArgs.isEmpty) Some((remBinders, acc)) else None
        }
      }

      loop(tp, args, Map()) match {
        case None =>
          Some(Left(s"Wrong instantiation of macro: $inst"))
        case Some((ty, m)) =>
          Some(Right(m.foldLeft(ty) {
            case (acc, (x, e)) => acc.replace(x,e)
          }))
      }

    case _ =>
      None
  }

  def inlineMacro(tp: Tree, id: Identifier, rest: Tree): Either[String,Tree] = {
    rest.replace(subTree => macroTypeInst(id, tp, subTree))
  }

  val InferMacroTypeDecl = Rule("InferMacroTypeDecl", {
    case g @ InferGoal(c, t @ MacroTypeDecl(tp, Bind(id, rest))) =>
      TypeChecker.debugs(g, "InferMacroTypeDecl")
      inlineMacro(tp, id, rest) match {
        case Left(error) =>
          Some((
            List(),
            _ => emitErrorWithJudgment("InferMacroTypeDecl", g, Some(error))
          ))
        case Right(inlined) =>
          Some((
            List(_ => InferGoal(c.incrementLevel, inlined)), {
              case InferJudgment(_, _, _, ty, _) :: _ =>
                (true, InferJudgment("InferMacroTypeDecl", c, t, ty))
              case _ =>
                emitErrorWithJudgment("InferMacroTypeDecl", g, None)
            }
          ))
      }
    case g =>
      None
  })

}
