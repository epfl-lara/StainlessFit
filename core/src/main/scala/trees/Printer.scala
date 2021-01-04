/* Copyright 2019-2020 EPFL, Lausanne */

package fit
package core
package trees

import util.RunContext
import parser.FitParser
import parser._
import typechecker._

object Printer extends TreeToTokens with TokensToString {
  def asString(id: Identifier)(implicit rc: RunContext): String =
    if (rc.config.printUniqueIds) id.uniqueString else id.toString

  def asString(t: Tree)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (expr or type)") {
    tokensToString(treeToTokens(t))
  }

  def asString(ctx: Context)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (context)") {
    "Term variables:\n" ++
    ctx.termVariables.map {
      case (id, tp) => s"${asString(id)}: ${asString(tp)}"
    }.mkString("\n")
  }

  def asString(g: Goal)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (goal)") { g match {
    case EmptyGoal(_) => ""
    case ErrorGoal(_, _) => ""
    case InferGoal(c, t) => asString(t) + " ⇑ _"
    case CheckGoal(c, t, tp) => asString(t) + " ⇓ " + asString(tp)
    case SubtypeGoal(c, ty1, ty2) => asString(ty1) + " <: " + asString(ty2)
    case NormalizedSubtypeGoal(c, ty1, ty2) => asString(ty1) + " <:‖ " + asString(ty2)
    case NormalizationGoal(c, ty) => asString(ty) + s" ⇥ ?"
    case SynthesisGoal(c, tp) => s"_ ⇐ ${asString(tp)}"
    case EqualityGoal(c, t1, t2) => asString(t1) + " ≡ " + asString(t2)
  }}

  def exprInfo(t: Tree)(implicit rc: RunContext): Unit = {
    rc.reporter.info(asString(t))
  }

  def exprDebug(t: Tree)(implicit rc: RunContext): Unit = {
    rc.reporter.debug(asString(t))
  }
}

trait TreeToTokens {
  import TreeBuilders._
  import SDepSugar._

  private class Serializer(implicit rc: RunContext) {
    val tokens = collection.mutable.ArrayBuffer[Token]()

    def I(id: Identifier): Unit = { tokens += TermIdentifierToken(Printer.asString(id)) }
    def N(name: String): Unit = { tokens += TermIdentifierToken(name) }
    def K(kw: String): Unit = { tokens += KeywordToken(kw) }
    def Eq(): Unit = { tokens += EqualityToken }
    def S(sep: String): Unit = { tokens += SeparatorToken(sep) }
    def Ps(f: => Unit): Unit = { S("("); f; S(")") } // Parens
    def Bs(f: => Unit): Unit = { S("{"); f; S("}") } // Braces
    def Er(f: => Unit): Unit = { S("["); f; S("]") } // Erased (Brackets)

    def DA(arg: DefArgument): Unit = Ps {
      arg match {
        case TypeArgument(id) => I(id)
        case ForallArgument(id, tp) => I(id); Er { T(tp) }
        case UntypedArgument(id) => I(id)
        case TypedArgument(id, tp) => I(id); Er { T(tp) }
      }
    }

    def AA(arg: AppArgument): Unit =
      arg match {
        case TypeAppArg(tp) => T(tp)
        case AppArg(t) => T(t)
        case ErasableAppArg(t) => T(t)
      }

    // Optional type annotation
    def OTy(optTp: Option[Tree]): Unit =
      optTp foreach { tp => Er { T(tp) } }

    // Potentially omittable wrapping parens (to be done)
    def WrapPs(f: => Unit): Unit = Ps(f)

    def Tsep(ts: Seq[Tree], sep: => Unit): Unit =
      ts match {
        case t0 :: ts => T(t0); ts.foreach { t => sep; T(t) }
        case _ =>
      }

    def T(t: Tree): Unit = {
      t match {
        // === ScalaDep-specific treess

        case `LList` => N("LList")
        case SingletonType(`LList`, LNil()) => Bs { N("nil") }
        case LConsType(tp1, tp2) => N("LCons"); Er { T(tp1); S(","); T(tp2) }

        case NatMatchType(tp, tp1, Bind(id, tp2)) =>
          N("NatMatch"); T(tp)
          Bs {
            K("case"); K("zero"); S("=>"); T(tp1)
            K("case"); K("succ"); I(id); S("=>"); T(tp2)
          }
        case ListMatchType(tp, tp1, Bind(idHead, Bind(idTail, tp2))) =>
          N("ListMatch"); T(tp)
          Bs {
            K("case"); K("nil"); S("=>"); T(tp1)
            K("case"); K("cons"); I(idHead); I(idTail); S("=>"); T(tp2)
          }

        case Choose(tp) => N("choose"); Er { T(tp) }
        case ChooseWithPath(tp, t) => N("choose"); Er { T(tp) }; Ps { T(t) }

        case SingletonType(tp, t) =>
          if (rc.config.printUnderlying)
            Bs { Er { T(tp) }; T(t) }
          else
            Bs { Er { S("...") }; T(t) }

        case LNil() =>
          N("nil")
        case LConses(tElems, tBase) =>
          WrapPs { tElems.foreach { t => T(t); S("::") }; T(tBase) }
        case ListMatch(t, t1, Bind(idHead, Bind(idTail, t2))) =>
          K("list_match"); T(t)
          Bs {
            K("case"); K("nil"); S("=>"); T(t1)
            K("case"); K("cons"); I(idHead); I(idTail); S("=>"); T(t2)
          }

        case FixWithDefault(tp, Bind(id, t), td, tf) =>
          K("fixD")
          Ps { I(id); Er { T(tp) }; S("=>"); T(t); S(","); S("...") }
          Ps { T(tf) }

        case Ascribe(t, tp) =>
          Ps { T(t) }
          S(":")
          Er { T(tp) }

        // === General StainlessFit trees

        case Var(id) => I(id)
        case NatLiteral(n: BigInt) => tokens += NumberToken(n)
        case UnitLiteral => S("("); S(")")
        case BooleanLiteral(b) => tokens += BooleanToken(b)

        case Abstractions(args, e) if args.nonEmpty =>
          K("fun of"); args.foreach(DA); Eq(); Bs { T(e) }
        case Applications(e, args) if args.nonEmpty =>
          T(e); args.foreach(AA)
        case Node(name, children) =>
          N(name); WrapPs { Tsep(children, S(",")) }

        case Pair(t1, t2) =>
          Ps { T(t1); S(","); T(t2) }
        case Succ(t) => WrapPs { N("succ"); T(t) }
        case Size(t) => WrapPs { N("size"); T(t) }
        case First(t) => WrapPs { N("first"); T(t) }
        case Second(t) => WrapPs { N("second"); T(t) }
        case LeftTree(t) => WrapPs { N("left"); T(t) }
        case RightTree(t) => WrapPs { N("right"); T(t) }

        case Fix(None, Bind(f, body)) =>
          K("fix"); Ps { I(f); S("=>"); T(body) }
        case Fix(Some(Bind(n, tp)), Bind(_, Bind(f, body))) =>
          K("fix")
          Er { I(n) }
          Er { T(tp) }
          Ps { I(f); S("=>"); T(body) }

        case IfThenElse(cond, t1, t2) =>
          K("if"); Ps { T(cond) }; Bs { T(t1) }; K("else"); Bs { T(t2) }
        case NatMatch(t, t1, Bind(n, t2)) =>
          K("nat_match"); T(t)
          Bs {
            K("case"); K("zero"); S("=>"); T(t1)
            K("case"); K("succ"); I(n); S("=>"); T(t2)
          }
        case EitherMatch(t, Bind(x1, t1), Bind(x2, t2)) =>
          K("either_match"); T(t)
          Bs {
            K("case"); K("left"); I(x1); S("=>"); T(t1)
            K("case"); K("right"); I(x2); S("=>"); T(t2)
          }

        case LetIn(optTp, value, Bind(x, body)) =>
          K("val"); I(x); OTy(optTp); Eq(); T(value); S(";"); T(body)
        case Unfold(value, Bind(x, body)) =>
          K("[unfold]"); K("val"); I(x); Eq(); T(value); S(";"); T(body)
        case UnfoldPositive(value, Bind(x, body)) =>
          K("[unfold positive]"); K("val"); I(x); Eq(); T(value); S(";"); T(body)
        case Fold(tp, t) =>
          Er { K("fold"); K("as"); T(tp) }; Ps { T(t) }

        case Error(msg, optTp) =>
          K("error"); OTy(optTp); Ps { S("\""); tokens += StringToken(msg); S("\"") }

        case Primitive(op, List(t1)) => tokens += OperatorToken(op); T(t1)
        case Primitive(op, List(t1, t2)) => WrapPs { T(t1); tokens += OperatorToken(op); T(t2) }

        case BottomType => tokens += TypeToken("Bottom")
        case TopType => tokens += TypeToken("Top")
        case UnitType => tokens += TypeToken("Unit")
        case BoolType => tokens += TypeToken("Bool")
        case NatType => tokens += TypeToken("Nat")

        case SigmaType(tp1, Bind(x, tp2)) =>
          K("Sigma"); Ps { I(x); S(":"); T(tp1); S(","); T(tp2) }
        case PiType(tp1, Bind(x, tp2)) =>
          K("Pi"); Ps { I(x); S(":"); T(tp1); S(","); T(tp2) }
        case ExistsType(tp1, Bind(x, tp2)) =>
          K("Exists"); Ps { I(x); S(":"); T(tp1); S(","); T(tp2) }
        case IntersectionType(tp1, Bind(x, tp2)) =>
          K("Forall"); Ps { I(x); S(":"); T(tp1); S(","); T(tp2) }
        case PolyForallType(Bind(x, tp)) =>
          K("PolyForall"); Ps { I(x); S(","); T(tp) }
        case RefinementType(tp1, Bind(x, tp2)) =>
          Bs { I(x); Er { T(tp1) }; S("|"); T(tp2) }
        case RefinementByType(tp1, Bind(x, tp2)) =>
          S("{{"); I(x); Er { T(tp1) }; S("|"); T(tp2); S("}}")
        case RecType(t, Bind(a, tp)) =>
          K("rec"); Ps { T(t) }; Ps { I(a); S("=>"); T(tp) }
        case SumType(tp1, tp2) =>
          T(tp1); tokens += OperatorToken(Plus); T(tp2)
        case UnionType(tp1, tp2) =>
          T(tp1); tokens += OperatorToken(Cup); T(tp2)
        case EqualityType(tp1, tp2) =>
          Er { T(tp1); Eq(); T(tp2) }

        // Not sure we should have this case:
        case Bind(id, body) => I(id); S("@=>"); T(body)

        // Shouldn't get here
        case Lambda(tp, bind) => ???
        case ErasableLambda(ty, bind) => ???
        case Abs(t) => ???
        case App(t1, t2) => ???
        case TypeApp(t1, t2) => ???
        case ErasableApp(t1, t2) => ???
        case MacroTypeDecl(tp, body) => ???
        case MacroTypeInst(v, args) => ???
        case Fix(optAnnot, bind) => ???
        case NatMatch(t, t1, t2) => ???
        case EitherMatch(t, t1, t2) => ???
        case Primitive(op, args) => ???
        case Refl(t1, t2) => ???
        case Because(t1, t2) => ???
      }
    }
  }

  def treeToTokens(t: Tree)(implicit rc: RunContext): Seq[Token] = {
    val s = new Serializer
    s.T(t)
    s.tokens.toSeq
  }
}

trait TokensToString {
  def tokenToString(t: Token): String = t match {
    case SeparatorToken(s) => s
    case KeywordToken("funof") => "fun of"
    case KeywordToken("[unfoldpositive]") => "[unfold positive]"
    case KeywordToken(s) => s
    case TypeIdentifierToken(content) => content
    case TermIdentifierToken(content) => content
    case EqualityToken => "="
    case TypeToken(content) => content
    case OperatorToken(op) => op.toString
    case UnitToken => "()"
    case NumberToken(value) => value.toString
    case BooleanToken(value) => value.toString
    case StringToken(value) => value
    case _ => throw new Exception(s"Token $t is not supported by the pretty printer")
  }

  object OpeningBracket {
    def unapply(t: Token): Boolean =
      t == SeparatorToken("[")  ||
      t == SeparatorToken("{")  ||
      t == SeparatorToken("[|") ||
      t == SeparatorToken("(")
  }

  object ClosingBracket {
    def unapply(t: Token): Boolean =
      t == SeparatorToken("]")  ||
      t == SeparatorToken("}")  ||
      t == SeparatorToken("|]") ||
      t == SeparatorToken(")")
  }

  object LiteralToken {
    def unapply(t: Token): Boolean = t match {
      case UnitToken => true
      case NumberToken(_) => true
      case BooleanToken(_) => true
      case _ => false
    }
  }

  def insertSpace(t1: Token, t2: Token): Boolean = (t1, t2) match {
    case (KeywordToken("val"), _) => true
    case (KeywordToken("fun"), _) => true
    case (TermIdentifierToken(_), KeywordToken("fun of")) => true
    case (KeywordToken("[fold"), _) => true
    case (KeywordToken("[unfold]"), _) => true
    case (KeywordToken("[unfoldpositive]"), _) => true
    case (KeywordToken("[decreases"), _) => true
    case (KeywordToken("as"), _) => true
    case (KeywordToken("type"), _) => true
    case (KeywordToken("as"), _) => true
    case (KeywordToken("if"), _) => true
    case (KeywordToken("else"), _) => true
    case (KeywordToken("keep"), _) => true
    case (KeywordToken("funof"), _) => true
    case (KeywordToken("case"), _) => true
    case (_, KeywordToken("case")) => true
    case (KeywordToken("left"), _) => true
    case (KeywordToken("right"), _) => true
    case (KeywordToken("succ"), _) => true
    case (KeywordToken("cons"), _) => true
    case (KeywordToken("match"), _) => true
    case (KeywordToken("nat_match"), _) => true
    case (KeywordToken("Nat_Match"), _) => true
    case (KeywordToken("list_match"), _) => true
    case (KeywordToken("List_Match"), _) => true
    case (KeywordToken("[returns"), _) => true
    case (_, KeywordToken("[returns")) => true

    case (SeparatorToken(","), _) => true
    case (SeparatorToken(":"), _) => true
    case (SeparatorToken("{"), _) => true
    case (_, SeparatorToken("}")) => true
    case (SeparatorToken("=>"), _) => true
    case (_, SeparatorToken("=>")) => true
    case (SeparatorToken("|"), _) => true
    case (_, SeparatorToken("|")) => true

    case (OperatorToken(_), _) => true
    case (_, OperatorToken(_)) => true

    case (EqualityToken, _) => true
    case (_, EqualityToken) => true

    case (SeparatorToken(")"), SeparatorToken("{")) => true

    case (SeparatorToken("::"), NumberToken(_)) => false
    case (SeparatorToken("::"), _) => true
    case (NumberToken(_), SeparatorToken("::")) => false
    case (_, SeparatorToken("::")) => true

    case (TermIdentifierToken(_), LiteralToken()) => true
    case (LiteralToken(), TermIdentifierToken(_)) => true

    case (ClosingBracket(), LiteralToken()) => true
    case (LiteralToken(), OpeningBracket()) => true

    case (TermIdentifierToken(_), OpeningBracket()) => true
    case (TypeIdentifierToken(_), OpeningBracket()) => true

    case (ClosingBracket(), TermIdentifierToken(_)) => true
    case (ClosingBracket(), TypeIdentifierToken(_)) => true

    case (TermIdentifierToken(_), TermIdentifierToken(_)) => true
    case (TypeIdentifierToken(_), TermIdentifierToken(_)) => true
    case (TermIdentifierToken(_), TypeIdentifierToken(_)) => true
    case (TypeIdentifierToken(_), TypeIdentifierToken(_)) => true
    case _ => false
  }

  def allowNewLine(t: Token): Boolean = t != SeparatorToken(";")
  def allowNewLine(ts: Seq[Token]): Boolean = ts.isEmpty || allowNewLine(ts(0))

  def tokensToString(l: Iterator[Token])(implicit rc: RunContext): String = {
    tokensToString(l.toSeq)
  }

  def tokensToString(l: Seq[Token])(implicit rc: RunContext): String = {

    val res = new StringBuilder()

    def loop(indentation: String, rest: Seq[Token]): Unit = rest match {
      case Nil => ()
      case t +: ts =>
        val newIndentation = Indentation.update(indentation, t.indentation)

        if (t.indentation == Indentation.Unindent)
          res.append("\n" + newIndentation)

        res.append(t.before)
        if (t.before.endsWith("\n"))
          res.append(newIndentation)

        res.append(tokenToString(t))

        if (!ts.isEmpty) {

          if (t.after.isEmpty) {
            if (insertSpace(t, ts.head))
              res.append(" ")
          }
          else {
            val after = if (allowNewLine(ts)) t.after else t.after.replace("\n", "")
            res.append(after)
            if (!after.isEmpty && after.last == '\n' && !ts.isEmpty)
              res.append(newIndentation)
          }

          loop(newIndentation, ts)
        }
    }

    rc.bench.time("tokensToString"){ loop("", l) }
    res.toString()
  }
}
