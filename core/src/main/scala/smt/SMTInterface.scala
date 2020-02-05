// package stainlessfit
// package core

// import smtlib.trees.Terms. {
//   Identifier => TermIdentifier,
//   _
// }
// import smtlib.trees.Commands._
// import smtlib.theories.Core. {
//   And => TermAnd,
//   Or => TermOr,
//   Implies => TermImplies,
//   Not => TermNot,
//   Equals => TermEquals,
//   _
// }
// import smtlib.theories.Ints. {
//   Div => TermDiv,
//   Mod => TermMod,
//   _
// }
// import smtlib.printer.RecursivePrinter

// import scala.language.postfixOps

// import java.io.{File, Writer}

// import sys.process._

// import trees._

// object SMTInterface {
//   def sy(s: String) = SSymbol(s)
//   def si(s: SSymbol) = SimpleIdentifier(s)
//   def t(s: SSymbol): QualifiedIdentifier = QualifiedIdentifier(si(s))
//   def t(s: String): Term = t(sy(s))

//   implicit class SymbolDecoration(s: SSymbol) {
//     def apply(ts: Term*) = FunctionApplication(t(s), ts.toSeq)
//   }

//   def treeToTerm(e: Tree): Term = e match {
//     case BooleanLiteral(false) => t("false")
//     case BooleanLiteral(true) => t("true")
//     case NatLiteral(i) => SNumeral(i)
//     case UnaryMinus(e0) => Neg(treeToTerm(e0))
//     case And(e1, e2) => TermAnd(treeToTerm(e1), treeToTerm(e2))
//     case Or(e1, e2) => TermOr(treeToTerm(e1), treeToTerm(e2))
//     case Implies(e1, e2) => TermImplies(treeToTerm(e1), treeToTerm(e2))
//     case Not(e0) => TermNot(treeToTerm(e0))
//     case Plus(e1, e2) => Add(treeToTerm(e1), treeToTerm(e2))
//     case Minus(e1, e2) => Sub(treeToTerm(e1), treeToTerm(e2))
//     case Mult(e1, e2) => Mul(treeToTerm(e1), treeToTerm(e2))
//     case Div(e1, e2) => TermDiv(treeToTerm(e1), treeToTerm(e2))
//     case Mod(e1, e2) => TermMod(treeToTerm(e1), treeToTerm(e2))
//     case Equals(e1, e2) => TermEquals(treeToTerm(e1), treeToTerm(e2))
//     case Geq(e1, e2) => GreaterEquals(treeToTerm(e1), treeToTerm(e2))
//     case Gt(e1, e2) => GreaterThan(treeToTerm(e1), treeToTerm(e2))
//     case Leq(e1, e2) => LessEquals(treeToTerm(e1), treeToTerm(e2))
//     case Lt(e1, e2) => LessThan(treeToTerm(e1), treeToTerm(e2))
//     case Var(Identifier(name)) => t(name)
//     case Old(_) => throw new Exception("`Old` cannot be translated to SMT")
//   }

//   def typeToSort(t: Type): Sort = t match {
//     case BoolType => BoolSort()
//     case BigIntType => IntSort()
//   }

//   def treeToSMT(fresh: Int, vds: Seq[VarDef], args: Seq[Arg], e: Tree, writer: Writer): Unit = {
//     def pc(c: Command) = RecursivePrinter.printCommand(c, writer)
//     def passert(t: Term) = pc(Assert(t))

//     for (vd <- vds) {
//       for (suffix <- "" +: "'" +: (1 until fresh).map("#" + _))
//         pc(DeclareConst(sy(vd.id.name + suffix), typeToSort(vd.tpe)))
//     }

//     for (arg <- args) {
//       pc(DeclareConst(sy(arg.id.name), typeToSort(arg.tpe)))
//     }

//     passert(treeToTerm(e))

//     pc(CheckSat())

//     writer.close()
//   }

//   def exec(cmd: String): (Int, String) = {
//     var output = ""
//     val code = cmd ! ProcessLogger(s => { output += s + "\n"});
//     (code, output)
//   }

//   def invokeZ3(file: File): Boolean = {
//     val (code, output) = exec(s"""z3 dump-models=true "${file.getPath}"""")
//     if (code != 0)
//       throw new Exception(s"Error (code $code) in Z3:\n$output")
//     else if (output.contains("unsat")) true
//     else {
//       reporter.error("Z3 returned a satisfying model:")
//       reporter.error("===============================")
//       reporter.error(output)
//       reporter.error("===============================")
//       false
//     }
//   }
// }
