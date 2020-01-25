package core
package typechecker

object TypeCheckerSMTRules {
  // 
  // val Z3ArithmeticSolver: Rule = Rule("Z3ArithmeticSolver", {
  //   case g @ EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, t1 ::  t2 ::  Nil)) =>
  //     TypeChecker.debugs(g, "Z3ArithmeticSolver")
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
