package stainlessfit
package core
package typechecker

import stainlessfit.core.trees._
import stainlessfit.core.typechecker.Derivation.{AreEqualJudgment, emitErrorWithJudgment}
import stainlessfit.core.util.RunContext

trait SMTRules {

  implicit val rc: RunContext

  def addNatSubtree(subtrees: scala.collection.mutable.Map[Tree, Tree], termVariables: Map[Identifier, Tree], tree: Tree): Unit =
    tree match {
      case _: NatLiteral => ()
      case Primitive(op, n1 :: n2 :: Nil) if op.isNatToNatBinOp =>
        addNatSubtree(subtrees, termVariables, n1)
        addNatSubtree(subtrees, termVariables, n2)
      case _ => subtrees(tree) = NatType
    }

  def addBoolSubtree(subtrees: scala.collection.mutable.Map[Tree, Tree], termVariables: Map[Identifier, Tree], tree: Tree): Unit =
    tree match {
      case _: BooleanLiteral => ()
      case Primitive(Eq | Neq, t1 :: t2 :: Nil) =>
        if (isNatExpression(termVariables, t1) || isNatExpression(termVariables, t2)) {
          addNatSubtree(subtrees, termVariables, t1)
          addNatSubtree(subtrees, termVariables, t2)
        } else if (isNatPredicate(termVariables, t1) || isNatPredicate(termVariables, t2)) {
          addBoolSubtree(subtrees, termVariables, t1)
          addBoolSubtree(subtrees, termVariables, t2)
        } else
          subtrees(tree) = BoolType
      case Primitive(op, t1 :: t2 :: Nil) if op.isNatToBoolBinOp =>
        addNatSubtree(subtrees, termVariables, t1)
        addNatSubtree(subtrees, termVariables, t2)
      case Primitive(op, t1 :: t2 :: Nil) if op.isBoolToBoolBinOp =>
        addBoolSubtree(subtrees, termVariables, t1)
        addBoolSubtree(subtrees, termVariables, t2)
      case Primitive(op, t1 :: Nil) if op.isBoolToBoolUnOp =>
        addBoolSubtree(subtrees, termVariables, t1)
      case _ => subtrees(tree) = BoolType
    }

  def isNatExpression(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case Var(id) => termVariables.contains(id) && TypeOperators.dropRefinements(termVariables(id)) == NatType
      case NatLiteral(_) => true
      case Size(_) => true
      case Primitive(op, _ :: _ :: Nil) => op.isNatToNatBinOp
      case _ => false
    }
  }

  def isNatPredicate(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case Var(id) => termVariables.contains(id) && TypeOperators.dropRefinements(termVariables(id)) == BoolType
      case BooleanLiteral(_) => true
        // polymorphic operations
      case Primitive(Eq | Neq, _) => true
      case Primitive(op, _ :: _ :: Nil) => op.isNatToBoolBinOp || op.isBoolToBoolBinOp
      case Primitive(op, _ :: Nil) => op.isBoolToBoolUnOp
      case _ => false
    }
  }

  def isNatOrBoolEquality(termVariables: Map[Identifier, Tree], left: Tree, right: Tree): Boolean = {
    (isNatPredicate(termVariables, left) && isNatPredicate(termVariables, right)) ||
      (isNatExpression(termVariables, left) && isNatExpression(termVariables, right))
  }

  val Z3ArithmeticSolver: Rule = Rule("SMTSolver", {
    case g@EqualityGoal(c, t1, t2) if isNatOrBoolEquality(c.termVariables, t1, t2) =>
      val solver = new SMTInterface("smt-sessions/tmp.smt")
      // Subtrees whose structure the solver can't understand (for example, size(t)), which are therefore just declared
      // as variables of the corresponding type
      val subtrees = scala.collection.mutable.Map[Tree, Tree]()
      var assertions = Seq[Tree]()

      c.termVariables.foreach { case (id, tp) =>
        tp match {
          case EqualityType(h1, h2) if isNatOrBoolEquality(c.termVariables, h1, h2) =>
            addBoolSubtree(subtrees, c.termVariables, Primitive(Eq, h1 :: h2 :: Nil))
            assertions = Primitive(Eq, h1 :: h2 :: Nil) +: assertions
          case _ => ()
        }
      }

      solver.declareVariables(subtrees.toMap)
      solver.addAssertions(assertions)

      val subgoals = scala.collection.mutable.Map[Tree, Tree]()
      addBoolSubtree(subgoals, c.termVariables, Primitive(Eq, t1 :: t2 :: Nil))
      solver.declareVariables(subgoals.toMap)

      solver.addAssertion(Primitive(Not, Primitive(Eq, t1 :: t2 :: Nil) :: Nil))

      if (solver.isSatisfiable) {
        None
      } else {
        Some((subgoals.map{case (t, typ) => (_: List[Derivation.Judgment]) => CheckGoal(c.incrementLevel, t, typ)
        }.toList, {
          case l: List[Derivation.CheckJudgment] if l.forall({
            case _: Derivation.CheckJudgment => true
            case _ => false
          }) =>
            (true, AreEqualJudgment("SMTSolver", c, t1, t2, "Validated by SMT solver"))
          case _ => emitErrorWithJudgment("SMTSolver", g, None)
        }
        ))
      }
    case _ => None
  })
}
