package core
package typechecker

import util.RunContext

trait TypeCheckerSMTRules {

  val rc: RunContext

  // def isNatExpression(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
  //   t match {
  //     case Var(id) => termVariables.contains(id) && dropRefinements(termVariables(id)) == NatType
  //     case NatLiteral(_) => true
  //     case Primitive(op, n1 ::  n2 ::  Nil) =>
  //       op.isNatToNatBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)
  //     case _ => false
  //   }
  // }

  // def isNatPredicate(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
  //   t match {
  //     case BooleanLiteral(_) => true
  //     case Primitive(Eq, n1 ::  n2 ::  Nil) =>
  //       (isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
  //       (isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
  //     case Primitive(op, n1 ::  n2 ::  Nil) =>
  //       (op.isNatToBoolBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
  //       (op.isBoolToBoolBinOp && isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
  //     case Primitive(op, b ::  Nil) => op.isBoolToBoolUnOp && isNatPredicate(termVariables, b)
  //     case _ => false
  //   }
  // }
  // 
  // val Z3ArithmeticSolver: Rule = Rule("Z3ArithmeticSolver", {
  //   case g @ EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, t1 ::  t2 ::  Nil)) =>
  //     TypeChecker.debugs(rc, g, "Z3ArithmeticSolver")
  //     TypeChecker.z3Debug("Current goal:\n" + g)
  //     TypeChecker.z3Debug("Current context:\n" + c)
  //     TypeChecker.z3Debug("\nInvoking Z3\n")

  //     val factory = Solver.getFactory
  //     val z3 = factory.getContext
  //     val solver = z3.mkSolver
  //     val i = z3.mkIntSort

  //     val z3Variables =
  //       ListOps.toMap(c.variables.filter(v => dropRefinements(c.termVariables(v)) == NatType).map {
  //         id => id -> z3.mkConst(z3.mkStringSymbol(id.toString), i)
  //       })

  //     c.variables.map { v =>
  //       c.termVariables(v) match {
  //         case EqualityType(h1, h2) if isNatPredicate(c.termVariables, Primitive(Eq, h1 ::  h2 ::  Nil)) =>
  //           solver.assertCnstr(z3Encode(z3, solver, z3Variables, Primitive(Eq, h1 ::  h2 ::  Nil)))
  //         case _ => ()
  //       }
  //     }

  //     val b = z3Encode(z3, solver, z3Variables, Primitive(Eq, t1 ::  t2 ::  Nil))
  //     solver.assertCnstr(z3.mkNot(b))

  //     c.variables.filter(c.termVariables(_) == NatType).map { id =>
  //       val v = z3.mkConst(z3.mkStringSymbol(id.toString), i)
  //       solver.assertCnstr(z3.mkGE(v, z3.mkInt(0, i)))
  //     }

  //     TypeChecker.z3Debug(solver.toString)

  //     val solverResponse = solver.check

  //     TypeChecker.z3Debug("Response: " + solverResponse + "\n")

  //     val modelString = solverResponse match {
  //       case scala.None => ""
  //       case scala.Some(true) => solver.getModel.toString
  //       case scala.Some(false) => ""
  //     }

  //     Solver.reclaim(factory)

  //     solverResponse match {
  //       case scala.None =>
  //         None

  //       case scala.Some(true) =>
  //         None

  //       case scala.Some(false) => Some((List(), _ =>
  //         (true, AreEqualJudgment("Z3ArithmeticSolver", c, t1, t2, "Validated by Z3"))))
  //     }

  //   case g =>
  //     None
  // }

}
