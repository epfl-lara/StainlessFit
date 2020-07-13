package stainlessfit

package core
package util

import core.trees._
import core.typechecker.Derivation._
import core.typechecker._

import java.io.FileWriter
import java.io.File
import core.typechecker.EmptyGoal

object CoqOutput {
  
  def shortString(s: String, maxWidth: Int = 900): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  def termOutput(t: Tree)(implicit rc: RunContext): String =
    shortString(Printer.exprAsString(t))

  def typeOutput(t: Tree)(implicit rc: RunContext): String =
    shortString(Printer.typeAsString(t))

  def goalToCoq(g: Goal)(implicit rc: RunContext): String = g match {
    case EmptyGoal(_) => ""
    case ErrorGoal(_, _) => ""
    case InferGoal(c, t) => termOutput(t) + " Infer _"
    case CheckGoal(c, t, tp) => termOutput(t) + " Check " + typeOutput(tp)
    case SubtypeGoal(c, ty1, ty2) => typeOutput(ty1) + " <: " + typeOutput(ty2)
    case SynthesisGoal(c, tp) =>
      s"_ ⇐ ${typeOutput(tp)}"
    case EqualityGoal(c, t1, t2) =>
      termOutput(t1)+ " ≡ " + termOutput(t2)
  }

  def typecontextToCoq(context: Context): String = {
    if (context.typeVariables.isEmpty) {
      "nil"
    } else {
      "(" + context.typeVariables.foldRight("nil")({
        case (id, acc) => toCoqIndex(id).toString() +"::"+acc
      }) + ")"
    }
  }

    
  def termcontextToCoq(context: Context): String =  {
    if (context.termVariables.isEmpty) {
      "nil"
    } else {
       "(" +context.termVariables.foldRight("nil")({
        case ((id,tp), acc) => "(" + toCoqIndex(id).toString() +","+ treeToCoq(toNamelessRep(tp)(Map()))+")::"+acc
      })+ ")"
    }
  }

  def judgementToCoq(j: Judgment)(implicit rc: RunContext): String = j match {
    case CheckJudgment(name, context, t, tp, _) =>
        "( J (" + name + ") "+ typecontextToCoq(context) +" "+ termcontextToCoq(context) +" " + treeToCoq(toNamelessRep(t)(Map())) + " " + treeToCoq(toNamelessRep(tp)(Map())) + ")"

    case SubtypeJudgment(name, context, ty1, ty2) =>
        "(" + (context.level.toString) + " - " + (name) + ") ⊢ " +
        typeOutput(ty1) + " <: " + typeOutput(ty2) 

    case InferJudgment(name, context, t, tp, _) =>
        "( J (" + name+ ") "+ typecontextToCoq(context) +" "+ termcontextToCoq(context) +" " + treeToCoq(toNamelessRep(t)(Map())) + " " + treeToCoq(toNamelessRep(tp)(Map())) + ")"

    case AreEqualJudgment(name, context, t1, t2, _) =>
        "(" + (context.level.toString) + " - " + (name) + ") ⊢ " +
        termOutput(t1) + " ≡ " + termOutput(t2) 

    case SynthesisJudgment(name, context, tp, t) =>
      s"(${(context.level.toString)} - ${(name)}) ⊢ ${(shortString(t.toString))} ⇐ ${typeOutput(tp)}"

    case ErrorJudgment(name, goal, errOpt) =>
      val errorString = errOpt.map(err => s" [ERROR: $err]").mkString
      "(" + (goal.c.level.toString) + " - " + (name) + ") ⊢ " +
      goalToCoq(goal) + errorString 

    case EmptyJudgment(name, context) =>
      s""

    case FileJudgment(name, context, s) =>
      s"(${(context.level.toString)} - ${(name)}) ⊢ File ${(shortString(s))}"
  }

  def nodeTreeToCoq(l: List[NodeTree[Judgment]], depth: Int)(implicit rc: RunContext): String = 
  l match {
    case Nil => " nil"
    case _ => {
      val indentation = "  " * depth
      "\n" + indentation + l.map(t => nodeTreeToCoq(t, depth)).mkString("\n"+indentation+"::") + "::nil"
    }
  } 

  def nodeTreeToCoq(t: NodeTree[Judgment], depth: Int)(implicit rc: RunContext): String = {
    val childrenString = nodeTreeToCoq(t.children, depth + 1)
    s"(N ${judgementToCoq(t.node)}" +
      childrenString + ")" 
  }

  
  def makeCoqFile(file: File, trees: List[NodeTree[Judgment]], success: Boolean)(implicit rc: RunContext): Unit = {
    val coqfile = new File(file.getAbsolutePath() + ".v")
    val fw = new FileWriter(coqfile)
    val status = if (success) "Success" else "Failed"
    val name = file.getName()
    fw.write(s"(* Type Checking File $name: $status *)\n")
    fw.write(nodeTreeToCoq(trees, 0) + "\n")
    fw.close()
    rc.reporter.info(s"Created Coq file with derivations in: $coqfile")
  }

  def toCoqIndex(id: Identifier): Int = {
    id.name.foldLeft(0)({case (acc, c) => acc + c.toByte}) + id.id
  }
  def toCoqVarType(name: String): String = {
    if (name(0).isUpper) {
      "type_var"
    } else {
      "term_var"
    }
  }

  def levelUp(nameless: Map[Identifier, Int]): Map[Identifier, Int] = 
    nameless.map({case (id, n) => id -> (n+1)}).toMap


  def toNamelessRep(t: Tree)(implicit nameless: Map[Identifier, Int]): Tree = t match {

    case Var(id) if nameless.contains(id) => Var(Identifier(0, s"(lvar ${nameless(id)} ${toCoqVarType(id.name)})"))
    case Var(id) => Var(Identifier(0, s"(fvar ${toCoqIndex(id)} ${toCoqVarType(id.name)})"))
    case IfThenElse(cond, t1, t2) => IfThenElse(toNamelessRep(cond), toNamelessRep(t1), toNamelessRep(t2))
    case App(t1, t2) => App(toNamelessRep(t1), toNamelessRep(t2))
    case Pair(t1, t2) => Pair(toNamelessRep(t1), toNamelessRep(t2))
    case Size(t) => Size(toNamelessRep(t))
    case First(t) => First(toNamelessRep(t))
    case Second(t) => Second(toNamelessRep(t))
    case LeftTree(t) => LeftTree(toNamelessRep(t))
    case RightTree(t) => RightTree(toNamelessRep(t))
    case Bind(y, e) => Bind(y,toNamelessRep(e)(levelUp(nameless) + (y->0))) 
    case Lambda(tp, bind) => Lambda(tp.map(toNamelessRep), toNamelessRep(bind))
    case Fix(tp, bind) => Fix(tp.map(toNamelessRep), toNamelessRep(bind)) 
    case LetIn(tp, v, bind) => LetIn(tp.map(toNamelessRep), toNamelessRep(v), toNamelessRep(bind)) 
    case MacroTypeDecl(tp, bind) => ???
    case MacroTypeInst(v, args) => ???
    case NatMatch(t, t0, bind) => NatMatch(toNamelessRep(t), toNamelessRep(t0), toNamelessRep(bind))
    case EitherMatch(t, bind1, bind2) => EitherMatch(toNamelessRep(t), toNamelessRep(bind1), toNamelessRep(bind2))
    case Primitive(op, args) => ???
    case Fold(tp, t) => Fold(toNamelessRep(tp), toNamelessRep(t))
    case Unfold(t, bind) => Unfold(toNamelessRep(t), toNamelessRep(bind))
    case UnfoldPositive(t, bind) => ???
    case Abs(bind) => Abs(toNamelessRep(bind))
    case ErasableApp(t1, t2) => ErasableApp(toNamelessRep(t1), toNamelessRep(t2))
    case TypeApp(abs, tp) => TypeApp(toNamelessRep(abs), toNamelessRep(tp))
    case Error(e, t) => Error(e, t.map(toNamelessRep))
    case DefFunction(args, optRet, optMeasure, body, rest) => ???
    case ErasableLambda(ty, bind) => ???

    case SumType(t1, t2) => SumType(toNamelessRep(t1), toNamelessRep(t2))
    case PiType(t1, bind) => PiType(toNamelessRep(t1), toNamelessRep(bind))
    case SigmaType(t1, bind) => SigmaType(toNamelessRep(t1), toNamelessRep(bind))
    case IntersectionType(t1, bind) => IntersectionType(toNamelessRep(t1), toNamelessRep(bind))
    case ExistsType(t1, bind) => ExistsType(toNamelessRep(t1), toNamelessRep(bind))
    case RefinementType(t1, bind) => RefinementType(toNamelessRep(t1), toNamelessRep(bind))
    case RefinementByType(t1, bind) => RefinementByType(toNamelessRep(t1), toNamelessRep(bind))
    case RecType(n, bind) => RecType(toNamelessRep(n), toNamelessRep(bind))
    case PolyForallType(bind) => PolyForallType(toNamelessRep(bind))
    case Node(name, args) => ???
    case EqualityType(t1, t2) => EqualityType(toNamelessRep(t1), toNamelessRep(t2))

    case BottomType => t
    case TopType => t
    case UnitType => t
    case BoolType => t
    case NatType => t
    case UnitLiteral => t 
    case NatLiteral(_) => t
    case BooleanLiteral(_) => t

  }


  def treeToCoq(t: Tree):String = t match {

    // terms 
    case Var(id) => id.name
    case UnitLiteral => "()"
    case NatLiteral(n) if (n.intValue == 0) => "zero"
    case NatLiteral(n) => s"(succ ${treeToCoq(NatLiteral(n-1))})"
    case Succ(t0) => s"(succ ${treeToCoq(t0)})"
    case BooleanLiteral(b) => s"t_${b.toString()}"
    case IfThenElse(cond, t1, t2) => s"(ite ${treeToCoq(cond)} ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case App(t1, t2) => s"(app ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case Lambda(None, Bind(id, body)) => s"(notype_lambda ${treeToCoq(body)})"
    case Lambda(Some(ty), Bind(id, body)) => s"(lambda ${treeToCoq(ty)} ${treeToCoq(body)})"
    case Pair(t1, t2) => s"(pp ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case First(t0) => s"(succ ${treeToCoq(t0)})"
    case Second(t0) => s"(succ ${treeToCoq(t0)})"
    case LetIn(Some(tp), v, body) => s"(tlet ${treeToCoq(v)} ${treeToCoq(tp)} ${treeToCoq(body)})"
    case LetIn(None, v, body) => s"(notype_tlet ${treeToCoq(v)} ${treeToCoq(body)})"

    // Binder
    case Bind(id, body) => treeToCoq(body) // Not sure about this one
    
    // types
    case BoolType => "T_bool"
    case NatType => "T_nat"
    case UnitType => "T_unit"
    case TopType => "T_top"
    case BottomType => "T_bottom"
    case SumType(t1, t2) => s"(T_sum ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case PiType(t1, t2) => s"(T_arrow ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case SigmaType(t1, t2) => s"(T_prod ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case RefinementType(t1, t2) => s"(T_refine ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case RefinementByType(t1, t2) => s"(T_type_refine ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case IntersectionType(t1, t2) => s"(T_intersection ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case UnionType(t1, t2) => s"(T_union ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case EqualityType(t1, t2) => s"(T_equiv ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case ExistsType(t1, t2) => s"(T_exists ${treeToCoq(t1)} ${treeToCoq(t2)})"

    case _ => s"NOCOQPRINT [${t.toString()}]"
  }
/*
  case class Succ(t: Tree) extends Tree
case object UnitLiteral extends Tree
case class BooleanLiteral(b: Boolean) extends Tree
case class Bind(id: Identifier, body: Tree) extends Tree
case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree
case class Lambda(tp: Option[Tree], bind: Tree) extends Tree
case class DefFunction(args: Seq[DefArgument], optRet: Option[Tree], optMeasure: Option[Tree], body: Tree, rest: Tree) extends Tree
case class ErasableLambda(ty: Tree, bind: Tree) extends Tree
case class App(t1: Tree, t2: Tree) extends Tree
case class Pair(t1: Tree, t2: Tree) extends Tree
case class Size(t: Tree) extends Tree
case class First(t: Tree) extends Tree
case class Second(t: Tree) extends Tree
case class Fix(tp: Option[Tree], bind: Tree) extends Tree
case class NatMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class LeftTree(t: Tree) extends Tree
case class RightTree(t: Tree) extends Tree
case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree
case class MacroTypeDecl(tp: Tree, body: Tree) extends Tree
case class MacroTypeInst(v: Tree, args: Seq[(Boolean, Tree)]) extends Tree
case class Error(s: String, t: Option[Tree]) extends Tree
case class Primitive(op: Operator, args: List[Tree]) extends Tree
case class ErasableApp(t1: Tree, t2: Tree) extends Tree
case class Refl(t1: Tree, t2: Tree) extends Tree
case class Fold(tp: Tree, t: Tree) extends Tree
case class Unfold(t: Tree, bind: Tree) extends Tree
case class UnfoldPositive(t: Tree, bind: Tree) extends Tree
case class Abs(t: Tree) extends Tree
case class TypeApp(t1: Tree, t2: Tree) extends Tree
case object BottomType extends Tree
case object TopType extends Tree
case object UnitType extends Tree
case object BoolType extends Tree
case object NatType extends Tree
case class SigmaType(t1: Tree, t2: Tree) extends Tree
case class SumType(t1: Tree, t2: Tree) extends Tree
case class PiType(t1: Tree, t2: Tree) extends Tree
case class IntersectionType(t1: Tree, t2: Tree) extends Tree
case class ExistsType(t1: Tree, t2: Tree) extends Tree
case class RefinementType(t1: Tree, t2: Tree) extends Tree
case class RefinementByType(t1: Tree, t2: Tree) extends Tree
case class RecType(n: Tree, bind: Tree) extends Tree
case class PolyForallType(t: Tree) extends Tree
case class UnionType(t1: Tree, t2: Tree) extends Tree
case class EqualityType(t1: Tree, t2: Tree) extends Tree
case class Because(t1: Tree, t2: Tree) extends Tree
case class Node(name: String, children: Seq[Tree]) extends Tree
*/
}
