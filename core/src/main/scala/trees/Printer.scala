package stainlessfit
package core
package trees

import util.RunContext
import parser.FitParser
import parser._
import typechecker.Context
import typechecker._

object Printer {

  def tokenToString(t: Token): String = t match {
    case SeparatorToken(s) => s
    case KeywordToken("funof") => "fun of"
    case KeywordToken("[unfoldpositive]") => "[unfold positive]"
    case KeywordToken("{case") => "{\ncase"
    case KeywordToken(s) => s
    case TypeIdentifierToken(content) => content
    case TermIdentifierToken(content) => content
    case EqualityToken => "="
    case TypeToken(content) => content
    case OperatorToken(op) => op.toString
    case UnitToken => "()"
    case NumberToken(value) => value.toString
    case BooleanToken(value) => value.toString
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

  def tokensToString(l: Seq[Token])(implicit rc: RunContext): String = {

    val res = new StringBuilder()

    def loop(indentation: String, rest: Seq[Token]): Unit = rest match {
      case Nil => ()
      case t +: ts =>
        val newIndentation = Indentation.update(indentation, t.indentation)

        if (t.indentation == Indentation.Unindent)
          res.append("\n" + newIndentation)

        res.append(tokenToString(t))

        if (t.after.isEmpty) {
          if (ts.isEmpty)
            res.append("\n" + newIndentation)
          else if (insertSpace(t, ts.head))
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

    rc.bench.time("tokensToString"){ loop("", l) }
    res.toString()
  }

  def asString(id: Identifier)(implicit rc: RunContext): String = {
    val Identifier(n, name) = id
    if (rc.config.printUniqueIds)
      s"$name#$n"
    else
      name
  }

  def itToString(t: Tree, it: Iterator[Seq[Token]])(implicit rc: RunContext): String = {
    if (it.hasNext)
      tokensToString(it.next())
    else {
      asStringDebug(t)
      // Should be unreachable code:
      rc.reporter.fatalError(s"The pretty printer does not handle expression: $t")
    }
  }

  val asStringMap = new collection.mutable.HashMap[Tree, String]()

  def exprAsString(t: Tree)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (expr)") {
    asStringMap.getOrElseUpdate(t, {
      val it = rc.exprPrinter(t)
      itToString(t, it)
    })
  }

  def typeAsString(t: Tree)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (type)") {
    asStringMap.getOrElseUpdate(t, {
      val it = rc.typePrinter(t)
      itToString(t, it)
    })
  }

  def exprOrTypeAsString(t: Tree)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (expr or type)") {
    asStringMap.getOrElseUpdate(t, {
      val it = rc.exprPrinter(t)
      if (it.isEmpty)
        typeAsString(t)
      else
        tokensToString(it.next())
    })
  }

  def asString(ctx: Context)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (context)") {
    "Term variables:\n" ++
    ctx.termVariables.map {
      case (id, tp) => s"${Printer.asString(id)}: ${Printer.typeAsString(tp)}"
    }.mkString("\n")
  }

  def asString(g: Goal)(implicit rc: RunContext): String = rc.bench.time("PrettyPrinter (goal)") { g match {
    case EmptyGoal(_) => ""
    case ErrorGoal(_, _) => ""
    case InferGoal(c, t) => exprAsString(t) + " ⇑ _"
    case CheckGoal(c, t, tp) =>
      exprAsString(t) + " ⇓ " + typeAsString(tp)
    case SynthesisGoal(c, tp) =>
      s"_ ⇐ ${typeAsString(tp)}"
    case EqualityGoal(c, t1, t2) =>
      exprAsString(t1) + " ≡ " + exprAsString(t2)
  }}

  def asStringDebug(t: Tree)(implicit rc: RunContext): Unit = {
    import rc.parser._

    val syntaxes: Seq[Syntax[Tree]] = Seq(
      primitiveType, parTypeExpr, piType, sigmaType, forallType, polyForallType,
      recType, refinementType, sums, arrows, equalityType, simpleTypeExpr,
      typeExpr, boolean, number, termVariable, typeVariable, unit, literal,
      defFunction, retTypeP, measureP, lambda, keep, error, fixpoint, fold,
      unfoldIn, unfoldPositiveIn, letIn, parExpr, application, macroTypeInst,
      eitherMatch, natMatch, notApplication, mulDivAnd, plusMinusOr, ltGtLeqGeq,
      termOrEquality, condition, optBracketExpr, bracketExpr, simpleExpr,
      macroTypeDeclaration, expr
    )

    t.traverse_post { e =>
      if (syntaxes.forall(s => rc.parser.PrettyPrinter(s)(e).isEmpty))
        rc.reporter.fatalError(s"The pretty printer does not handle subtree: $e")
    }
  }

  def exprInfo(t: Tree)(implicit rc: RunContext): Unit = {
    rc.reporter.info(exprAsString(t))
  }

  def exprDebug(t: Tree)(implicit rc: RunContext): Unit = {
    rc.reporter.debug(exprAsString(t))
  }
}
