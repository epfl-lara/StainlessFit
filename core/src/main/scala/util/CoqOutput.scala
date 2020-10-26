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

  var knownRules = Set[String]();
  var unknownRules = Set[String]();
  var unknownTerms = Set[Tree]();
  
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
    case _ => ""
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

    
  def termcontextToCoq(context: Context): String =  context.lastOp match {
    case Same => "Same"
    case Append(addedElements) => "(Append (" + 
      addedElements.foldRight("nil") {
        case ((id, t), acc) => s"(${toCoqIndex(id).toString()}, ${treeToCoq(toNamelessRep(t)(Map()))}) :: "+acc
      } + "))"
    case New(context) => "(New (" + 
      context.termVariables.foldLeft("nil") {
        case (acc, (id, t)) => s"(${toCoqIndex(id).toString()}, ${treeToCoq(toNamelessRep(t)(Map()))}) :: "+acc
      } + "))"
  }

  def printJudgement(name: String, context: Context, t: Tree, tp: Tree): String =
    "("+ name + " "+ typecontextToCoq(context) +" "+ termcontextToCoq(context) +" " + treeToCoq(toNamelessRep(t)(Map())) + " " + treeToCoq(toNamelessRep(tp)(Map())) + ")"

  def judgementName(coqName: Option[(String, Option[Tree])]): String = 
    coqName match {
      case None => ""
      case Some((s, None)) => s
      case Some((s, Some(t))) => s"(${s} ${treeToCoq(toNamelessRep(t)(Map()))})"
    }


  def judgementToCoq(j: Judgment)(implicit rc: RunContext): String = j match {

    // Infer and Check Judgements are considered as `Typing Judgements`
    case CheckJudgment(name, context, t, tp, None) => this.unknownRules += j.name ;printJudgement("TJ " + name, context, t, tp)
    case CheckJudgment(_, context, t, tp, coqName) => this.knownRules   += j.name ;printJudgement("TJ " + judgementName(coqName), context, t, tp)

    case InferJudgment(name, context, t, tp, None) => this.unknownRules += j.name ;printJudgement("TJ " + name, context, t, tp)
    case InferJudgment(_, context, t, tp, coqName) => this.knownRules   += j.name ;printJudgement("TJ " + judgementName(coqName), context, t, tp)

    // Subtyping judgments
    case SubtypeJudgment(name, context, t, tp, None) => this.unknownRules += j.name ;printJudgement("StJ " + name, context, t, tp)
    case SubtypeJudgment(_, context, t, tp, coqName) => this.knownRules   += j.name ;printJudgement("StJ " + judgementName(coqName), context, t, tp)

    // Equivalence judgements
    case AreEqualJudgment(name, context, t, tp, _, None) => this.unknownRules += j.name ;printJudgement("EJ " + name, context, t, tp)
    case AreEqualJudgment(_, context, t, tp, _, coqName) => this.knownRules   += j.name ;printJudgement("EJ " + judgementName(coqName), context, t, tp)

    // Unsupported in Coq yet :
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

      case _ => this.unknownRules += j.name ;"UNKNOWN"
  }

  def nodeTreeToCoq(l: List[NodeTree[Judgment]], depth: Int)(implicit rc: RunContext): String = 
  l match {
    case Nil => " nil"
    case _ => {
      val indentation = "  " * depth
      "\n" + indentation + "(" + l.map(t => nodeTreeToCoq(t, depth)).mkString("\n"+indentation+"::") + "::nil)"
    }
  } 

  def nodeTreeToCoq(t: NodeTree[Judgment], depth: Int)(implicit rc: RunContext): String = t match {
    case _ => {
      s"(N ${judgementToCoq(t.node)}" + nodeTreeToCoq(t.children, depth + 1) + ")" 
    }
  }

  
  def makeCoqFile(file: File, trees: List[NodeTree[Judgment]], success: Boolean)(implicit rc: RunContext): Unit = {
    val coqfile = new File(file.getAbsolutePath().replaceFirst("[.][^.]+$", "") + ".v")
    val fw = new FileWriter(coqfile)
    val status = if (success) "Success" else "Failed"
    val name = file.getName()

    fw.write(s"(* Type Checking File $name: $status *)\n\n")
    fw.write("Require Export SystemFR.Derivation.\n")
    fw.write("Definition ds : derivation := \n")
    fw.write(nodeTreeToCoq(trees.head, 0) + ".\n \n")
    fw.write("Lemma derivationValid: is_valid ds nil = true.\n")
    fw.write("Proof. compute. reflexivity. Qed.\n")
    fw.close()
    rc.reporter.info(s"Created Coq file with derivations in: $coqfile")
    /* rc.reporter.info(s"Known rules: ${knownRules.toList.sorted.foldRight("")({
      case (r, acc) => r + ", " + acc })}") */
    if (unknownTerms.nonEmpty)
      rc.reporter.error(s"Unknown terms: ${shortString(unknownTerms.foldRight("")({
        case (r, acc) => shortString(r.toString(), 30) + ", " + acc }), 100)}")
    if (unknownRules.nonEmpty)
      rc.reporter.error(s"Unknown rules: ${unknownRules.foldRight("")({
        case (r, acc) => r + ", " + acc })}")
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

    //case Var(Identifier(id, "")) => Var(Identifier(0, s"(fvar ${id} term_var)"))
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
    //case MacroTypeDecl(tp, bind) =>  ???
    //case MacroTypeInst(v, args) => ???
    case NatMatch(t, t0, bind) => NatMatch(toNamelessRep(t), toNamelessRep(t0), toNamelessRep(bind))
    case EitherMatch(t, bind1, bind2) => EitherMatch(toNamelessRep(t), toNamelessRep(bind1), toNamelessRep(bind2))
    case Primitive(op, args) => Primitive(op, args.map(toNamelessRep))
    case Fold(tp, t) => Fold(toNamelessRep(tp), toNamelessRep(t))
    case Unfold(t, bind) => Unfold(toNamelessRep(t), toNamelessRep(bind))
    //case UnfoldPositive(t, bind) => ???
    case Abs(bind) => Abs(toNamelessRep(bind))
    case ErasableApp(t1, t2) => ErasableApp(toNamelessRep(t1), toNamelessRep(t2))
    case TypeApp(abs, tp) => TypeApp(toNamelessRep(abs), toNamelessRep(tp))
    case Error(e, t) => Error(e, t.map(toNamelessRep))
    //case DefFunction(args, optRet, optMeasure, body, rest) => ???
    //case ErasableLambda(ty, bind) => ???

    case SumType(t1, t2) => SumType(toNamelessRep(t1), toNamelessRep(t2))
    case PiType(t1, bind) => PiType(toNamelessRep(t1), toNamelessRep(bind))
    case SigmaType(t1, bind) => SigmaType(toNamelessRep(t1), toNamelessRep(bind))
    case IntersectionType(t1, bind) => IntersectionType(toNamelessRep(t1), toNamelessRep(bind))
    case ExistsType(t1, bind) => ExistsType(toNamelessRep(t1), toNamelessRep(bind))
    case RefinementType(t1, bind) => RefinementType(toNamelessRep(t1), toNamelessRep(bind))
    case RefinementByType(t1, bind) => RefinementByType(toNamelessRep(t1), toNamelessRep(bind))
    case RecType(n, bind) => RecType(toNamelessRep(n), toNamelessRep(bind))
    case PolyForallType(bind) => PolyForallType(toNamelessRep(bind))
    //case Node(name, args) => ???
    case EqualityType(t1, t2) => EqualityType(toNamelessRep(t1), toNamelessRep(t2))

    case BottomType => t
    case TopType => t
    case UnitType => t
    case BoolType => t
    case NatType => t
    case UnitLiteral => t 
    case NatLiteral(_) => t
    case BooleanLiteral(_) => t

    case _ => {
      this.unknownTerms += t ;
      t
    }

  }


  def treeToCoq(t: Tree):String = t match {

    // terms 
    case Var(id) => id.name
    case UnitLiteral => "uu"
    case NatLiteral(n) if (n.intValue == 0) => "zero"
    case NatLiteral(n) => s"(succ ${treeToCoq(NatLiteral(n-1))})"
    case Succ(t0) => s"(succ ${treeToCoq(t0)})"
    case BooleanLiteral(b) => s"t${b.toString()}"
    case IfThenElse(cond, t1, t2) => s"(ite ${treeToCoq(cond)} ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case App(t1, t2) => s"(app ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case Fix(None, Bind(id, body)) => s"(notype_tfix ${treeToCoq(body)})"
    case Fix(Some(ty), Bind(id, body)) => s"(tfix ${treeToCoq(ty)} ${treeToCoq(body)})"
    case Lambda(None, Bind(id, body)) => s"(notype_lambda ${treeToCoq(body)})"
    case Lambda(Some(ty), Bind(id, body)) => s"(lambda ${treeToCoq(ty)} ${treeToCoq(body)})"
    case Pair(t1, t2) => s"(pp ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case First(t0) => s"(succ ${treeToCoq(t0)})"
    case Second(t0) => s"(succ ${treeToCoq(t0)})"
    case LetIn(Some(tp), v, body) => s"(tlet ${treeToCoq(v)} ${treeToCoq(tp)} ${treeToCoq(body)})"
    case LetIn(None, v, body) => s"(notype_tlet ${treeToCoq(v)} ${treeToCoq(body)})"
    case EitherMatch(t, t1, t2) => s"(sum_match ${treeToCoq(t)} ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case LeftTree(t) => s"(tleft ${treeToCoq(t)})"
    case RightTree(t) => s"(tright ${treeToCoq(t)})"
    case Primitive(op, arg1::Nil) => s"(unary_primitive ${op.coqName} ${treeToCoq(arg1)})"
    case Primitive(op, arg1::arg2::Nil) => s"(binary_primitive ${op.coqName} ${treeToCoq(arg1)} ${treeToCoq(arg2)})"
    case ErasableApp(t1,t2) => s"(forall_inst ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case Error(_, None) => "notype_err"
    case Error(_, Some(t)) => s"(err ${treeToCoq(t)})" 
    case Abs(t) => s"(type_abs ${treeToCoq(t)})"

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
    case IntersectionType(t1, t2) => s"(T_forall ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case PolyForallType(t) => s"(T_abs ${treeToCoq(t)})"
    case UnionType(t1, t2) => s"(T_union ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case EqualityType(t1, t2) => s"(T_equiv ${treeToCoq(t1)} ${treeToCoq(t2)})"
    case ExistsType(t1, t2) => s"(T_exists ${treeToCoq(t1)} ${treeToCoq(t2)})"

    case _ => this.unknownTerms+= t;  s"NOCOQPRINT [${shortString(t.toString(), 30)}]"
  }

}
