package stainlessfit
package core
package typechecker

import Derivation._
import util.RunContext

case class Rule(
  name: String,
  apply: Goal => Option[(
    List[List[Judgment] => Goal],
    List[Judgment] => (Boolean, Judgment))
  ]) {
  def t(rc: RunContext): Tactic[Goal, (Boolean, NodeTree[Judgment])] = Tactic { (g, subgoalSolver) =>
    rc.bench.time("Rule " + name)
    { apply(g) }.flatMap {
      case (sgs, merge) =>
        val subTrees: Option[(Boolean, List[NodeTree[Judgment]])] =
          sgs.foldLeft[Option[(Boolean, List[NodeTree[Judgment]])]](Some(true, List())) {
            case (accOpt, fsg) =>
              accOpt.flatMap {
                case (success, acc) =>
                  subgoalSolver(fsg(acc.map(_.node))).map {
                    case (subSuccess, subTree) =>
                      (success && subSuccess, acc :+ subTree)
                  }
              }
          }
        subTrees.map { case (success, l) =>
          val (mergeSuccess, mergeJudgment) = merge(l.map(_.node))
          (success && mergeSuccess, NodeTree(mergeJudgment, l))
        }
    }
  }
}
