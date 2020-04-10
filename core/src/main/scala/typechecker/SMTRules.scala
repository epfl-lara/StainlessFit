package stainlessfit
package core
package typechecker

import java.io.{File, PrintWriter}
import java.nio.file.Files

import stainlessfit.core.trees._
import stainlessfit.core.typechecker.Derivation.AreEqualJudgment
import stainlessfit.core.util.RunContext

trait SMTRules {

  val rc: RunContext

  def isNatExpression(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case Var(id) => termVariables.contains(id) && TypeOperators.dropRefinements(termVariables(id)) == NatType
      case NatLiteral(_) => true
      case Primitive(op, n1 :: n2 :: Nil) =>
        op.isNatToNatBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)
      case _ => false
    }
  }

  def isNatPredicate(termVariables: Map[Identifier, Tree], t: Tree): Boolean = {
    t match {
      case BooleanLiteral(_) => true
      case Primitive(Eq, n1 :: n2 :: Nil) =>
        (isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
          (isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
      case Primitive(op, n1 :: n2 :: Nil) =>
        (op.isNatToBoolBinOp && isNatExpression(termVariables, n1) && isNatExpression(termVariables, n2)) ||
          (op.isBoolToBoolBinOp && isNatPredicate(termVariables, n1) && isNatPredicate(termVariables, n2))
      case Primitive(op, b :: Nil) => op.isBoolToBoolUnOp && isNatPredicate(termVariables, b)
      case _ => false
    }
  }

  val Z3ArithmeticSolver: Rule = Rule("Z3ArithmeticSolver", {
    case g@EqualityGoal(c, t1, t2) if isNatPredicate(c.termVariables, Primitive(Eq, t1 :: t2 :: Nil)) =>
      val dir = new File("smt-sessions")
      if (!dir.exists) Files.createDirectory(dir.toPath)
      val out = dir.toPath.resolve("tmp.smt2").toFile
      val writer = new PrintWriter(out)

      c.termVariables.foreach { case (id, tp) =>
        if (TypeOperators.dropRefinements(tp) == NatType)
          SMTInterface.declareVar(id.toString, writer)
      }

      c.termVariables.foreach { case (id, tp) =>
        tp match {
          case EqualityType(h1, h2) if isNatPredicate(c.termVariables, Primitive(Eq, h1 :: h2 :: Nil)) =>
            SMTInterface.addAssertion(Primitive(Eq, h1 :: h2 :: Nil), writer)
          case _ => ()
        }
      }

      SMTInterface.addAssertion(Primitive(Not, Primitive(Eq, t1 :: t2 :: Nil) :: Nil), writer)

      c.termVariables.foreach { case (id, tp) =>
        if (TypeOperators.dropRefinements(tp) == NatType)
          SMTInterface.addAssertion(Primitive(Geq, Var(id) :: NatLiteral(0) :: Nil), writer)
      }

      if (SMTInterface.isSatisfiable(out, writer))
        None
      else
        Some((List(), _ =>
          (true, AreEqualJudgment("Z3ArithmeticSolver", c, t1, t2, "Validated by SMT solver"))))
    case _ => None
  })
}
