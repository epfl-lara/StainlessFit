package core
package typechecker

import core.trees._

import Derivation._
import util.Utils._

object TypeCheckerMetaRules {

  def macroTypeInst(id: Identifier, tp: Tree, inst: Tree): Option[Tree] = inst match {
    case MacroTypeInst(Var(`id`), args) =>
      def loop(remBinders: Tree, remArgs: Seq[(Boolean, Tree)], acc: Map[Identifier, Tree])
        : Option[(Tree, Map[Identifier, Tree])] = {
        remBinders match {
          case Bind(x, body) =>
            remArgs match {
              case (isTerm, e) +: es if isTerm == x.isTermIdentifier =>
                loop(body, es, acc.updated(x, e))
              case _ => None
            }
          case _ =>
            if (remArgs.isEmpty) Some((remBinders, acc)) else None
        }
      }

      loop(tp, args, Map()) match {
        case Some((ty, m)) =>
          Some(m.foldLeft(ty) {
            case (acc, (x, e)) => acc.replace(x,e)
          })
        case None =>
          println(s"Wrong instantiation of macro $inst")
          throw new Exception(s"Wrong instantiation of macro $inst")
      }

    case _ => None
  }

  def inlineMacro(tp: Tree, id: Identifier, rest: Tree): Tree = {
    rest.replace(subTree => macroTypeInst(id, tp, subTree))
  }

  val InferMacroTypeDecl = Rule("InferMacroTypeDecl", {
    case g @ InferGoal(c, t @ MacroTypeDecl(tp, Bind(id, rest))) =>
      TypeChecker.debugs(g, "InferMacroTypeDecl")
      Some((
        List(_ => InferGoal(c, inlineMacro(tp, id, rest))), {
          case InferJudgment(_, _, _, ty) :: _ =>
            (true, InferJudgment("InferMacroTypeDecl", c, t, ty))
          case _ =>
            (false, ErrorJudgment("InferMacroTypeDecl", c, g.toString))
        }
      ))
    case g =>
      None
  })

}
