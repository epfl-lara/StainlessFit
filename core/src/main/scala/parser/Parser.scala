package stainlessfit
package core
package parser

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

import core.trees._
import core.trees.TreeBuilders._

import util.Utils._
import util.RunContext
import stainlessfit.core.extraction.BuiltInIdentifiers
import typechecker.ScalaDepSugar._

sealed abstract class Indentation
object Indentation {
  case object Indent extends Indentation
  case object Unindent extends Indentation
  case object Same extends Indentation

  def update(s: String, indentation: Indentation): String = indentation match {
    case Same => s
    case Indent => "  " + s
    case Unindent => s.drop(2)
  }
}


sealed abstract class Token extends Positioned {
  var after: String = ""
  var indentation: Indentation = Indentation.Same

  def printWith(s: String): Token = {
    after = s
    this
  }

  def indent(): Token = {
    indentation = Indentation.Indent
    this
  }

  def unindent(): Token = {
    indentation = Indentation.Unindent
    this
  }

}

case object EqualityToken extends Token

case class KeywordToken(value: String) extends Token
case class SeparatorToken(value: String) extends Token
case class BooleanToken(value: Boolean) extends Token
case class NumberToken(value: BigInt) extends Token
case class StringToken(value: String) extends Token
case object NullToken extends Token
case object SpaceToken extends Token
case class UnknownToken(content: String) extends Token

case object UnitToken extends Token

case class TermIdentifierToken(content: String) extends Token
case class TypeIdentifierToken(content: String) extends Token

case class OperatorToken(op: Operator) extends Token
case class TypeToken(content: String) extends Token

object FitLexer extends Lexers with CharRegExps {
  type Token = parser.Token
  type Position = (Int, Int)

  val blank = many { elem(c => c == '\n' || c == ' ') }

  val lexer = Lexer(
    // Operators
    oneOf("-+/*!<>∪") | word("&&") |  word("||") |
    word("==") | word("!=") | word("<=") | word(">=")
    |> { (cs, r) => OperatorToken(Operator.fromString(cs.mkString).get).setPos(r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => EqualityToken.setPos(r) },

    // Keywords
    (elem('[') ~ blank ~ word("returns")) |
    (elem('[') ~ blank ~ word("fold")) |
    (elem('[') ~ blank ~ word("decreases")) |
    (elem('[') ~ blank ~ word("unfold") ~ blank ~ elem(']')) |
    (elem('[') ~ blank ~ word("unfold") ~ blank ~ word("positive") ~ elem(']')) |
    word("as") | word("fun of") | word("keep") |
    word("if") | word("else") | word("case") |
    word("match") | word("nat_match") |
    word("list_match") | word("List_Match") | word("Cons") |
    word("nil") | word("cons") | word("List") |
    word("fix") | word("fixD") | word("fun") | word("val") |
    word("error") |
    word("zero") | word("succ") |
    word("left") | word("right") | word("size") |
    word("Rec") | word("Pi") | word("Sigma") |
    word("Forall") | word("PolyForall") | word("Exists") |
    word("type")
      |> { (cs, r) => KeywordToken(cs.mkString.replaceAll("""[ \n]""", "")).setPos(r) },

    // Compound separator
    word("[|") | word("|]")
      |> { (cs, r) => SeparatorToken(cs.mkString).setPos(r) },

    // Separator
    word("{{") | word("}}") | oneOf("{},|().:;[]") | word("=>")
      |> { (cs, r) => SeparatorToken(cs.mkString).setPos(r) },

    // Space
    many1(whiteSpace)
      |> { (_, r) => SpaceToken.setPos(r) },

    // Booleans
    word("true")
      |> { (_, r) => BooleanToken(true).setPos(r) },
    word("false")
      |> { (_, r) => BooleanToken(false).setPos(r) },

    word("Bool") | word("Unit") | word("Nat") | word("Top")
      |>  { (cs, r) => TypeToken(cs.mkString).setPos(r) },

    // Term identifiers start with a lower case letter
    elem(c => c.isLetter && c.isLower) ~
    many { elem(c => c.isLetterOrDigit || c == '_' || c == '$') }
      |> { (cs, r) => TermIdentifierToken(cs.mkString).setPos(r) },

    // Type identifiers start with an upper case letter
    elem(c => c.isLetter && c.isUpper) ~
    many { elem(c => c.isLetterOrDigit || c == '_' || c == '$') }
      |> { (cs, r) => TypeIdentifierToken(cs.mkString).setPos(r) },

    elem('"') ~
    many {
      elem(c => c != '"' && c != '\\' && !c.isControl) |
      elem('\\') ~ (oneOf("\"\\/bfnrt") | elem('u') ~ hex.times(4))
    } ~
    elem('"')
      |> { (cs, r) => {
        val string = cs.mkString
        StringToken(string.slice(1, string.length - 1)).setPos(r)
      }},

    // Numbers
    elem('0') | (nonZero ~ many(digit))
      |> { (cs, r) => NumberToken(cs.mkString.toInt).setPos(r) },

    elem('/') ~ elem('/') ~ many { elem(c => c != '\n' )}
      |> { (_, r) => SpaceToken.setPos(r) },

  ) onError {
    (cs, r) => UnknownToken(cs.mkString).setPos(r)
  }

  def apply(it: Iterator[Char]): Iterator[Token] = {
    object LineColumnPositioner extends Positioner[Char, (Int, Int)] {
      val start: (Int, Int) = (1, 1)
      def increment(lineColumn: (Int, Int), character: Char) = {
        val (line, column) = lineColumn
        if (character == '\n') (line + 1, 1)
        else (line, column + 1)
      }
    }
    val source = Source.fromIterator(it, LineColumnPositioner)
    val tokens = lexer.spawn(source)
    tokens.filterNot(_ == SpaceToken)
  }
}

sealed abstract class TokenClass
case object TypeIdentifierClass extends TokenClass
case object TermIdentifierClass extends TokenClass
case class OperatorClass(op: Operator) extends TokenClass
case class SeparatorClass(value: String) extends TokenClass
case object BooleanClass extends TokenClass
case object NumberClass extends TokenClass
case object StringClass extends TokenClass
case object NoClass extends TokenClass
case object UnitClass extends TokenClass
case object EqualityClass extends TokenClass
case class KeywordClass(value: String) extends TokenClass
case class TypeClass(value: String) extends TokenClass

class FitParser()(implicit rc: RunContext) extends Syntaxes with Operators with ll1.Parsing with ll1.Debug with PrettyPrinting {

  type Token = parser.Token
  type Kind = parser.TokenClass

  import SafeImplicits._

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value) => SeparatorClass(value)
    case BooleanToken(value) => BooleanClass
    case NumberToken(value) => NumberClass
    case TypeIdentifierToken(content) => TypeIdentifierClass
    case TermIdentifierToken(content) => TermIdentifierClass
    case OperatorToken(op) => OperatorClass(op)
    case EqualityToken => EqualityClass
    case KeywordToken(value) => KeywordClass(value)
    case UnitToken => UnitClass
    case TypeToken(content) => TypeClass(content)
    case StringToken(content) => StringClass
    case _ => NoClass
  }

  val equal: Syntax[Unit] = elem(EqualityClass).unit(EqualityToken)
  val dlsbra: Syntax[Unit] = elem(SeparatorClass("[|")).unit(SeparatorToken("[|"))
  val drsbra: Syntax[Unit] = elem(SeparatorClass("|]")).unit(SeparatorToken("|]"))
  val lpar: Syntax[Unit] = elem(SeparatorClass("(")).unit(SeparatorToken("("))
  val rpar: Syntax[Unit] = elem(SeparatorClass(")")).unit(SeparatorToken(")"))
  val lbra: Syntax[Unit] = elem(SeparatorClass("{")).unit(SeparatorToken("{"))
  val rbra: Syntax[Unit] = elem(SeparatorClass("}")).unit(SeparatorToken("}"))
  val dlbra: Syntax[Unit] = elem(SeparatorClass("{{")).unit(SeparatorToken("{{"))
  val drbra: Syntax[Unit] = elem(SeparatorClass("}}")).unit(SeparatorToken("}}"))
  val lbraBlock: Syntax[Unit] = elem(SeparatorClass("{")).unit(SeparatorToken("{").printWith("\n").indent())
  val rbraBlock: Syntax[Unit] = elem(SeparatorClass("}")).unit(SeparatorToken("}").printWith("\n").unindent())
  val rbraBlock2: Syntax[Unit] = elem(SeparatorClass("}")).unit(SeparatorToken("}").printWith("\n\n").unindent())
  val lsbra: Syntax[Unit] = elem(SeparatorClass("[")).unit(SeparatorToken("["))
  val rsbra: Syntax[Unit] = elem(SeparatorClass("]")).unit(SeparatorToken("]"))
  val rsbraNewLine: Syntax[Unit] = elem(SeparatorClass("]")).unit(SeparatorToken("]").printWith("\n"))
  val rsbraNewLines: Syntax[Unit] = elem(SeparatorClass("]")).unit(SeparatorToken("]").printWith("\n\n"))
  val comma: Syntax[Unit] = elem(SeparatorClass(",")).unit(SeparatorToken(","))
  val pipe: Syntax[Unit] = elem(SeparatorClass("|")).unit(SeparatorToken("|"))
  val colon: Syntax[Unit] = elem(SeparatorClass(":")).unit(SeparatorToken(":"))
  val semicolon: Syntax[Unit] = elem(SeparatorClass(";")).unit(SeparatorToken(";").printWith("\n"))
  val dot: Syntax[Unit] = elem(SeparatorClass(".")).unit(SeparatorToken("."))
  val arrow: Syntax[Unit] = elem(SeparatorClass("=>")).unit(SeparatorToken("=>"))
  val ifK: Syntax[Unit] = elem(KeywordClass("if")).unit(KeywordToken("if"))
  val elseK: Syntax[Unit] = elem(KeywordClass("else")).unit(KeywordToken("else"))
  val fixK: Syntax[Unit] = elem(KeywordClass("fix")).unit(KeywordToken("fix"))
  val fixDK: Syntax[Unit] = elem(KeywordClass("fixD")).unit(KeywordToken("fixD"))
  val funK: Syntax[Unit] = elem(KeywordClass("fun")).unit(KeywordToken("fun"))
  val funOfK: Syntax[Unit] = elem(KeywordClass("funof")).unit(KeywordToken("funof"))
  val matchK: Syntax[Unit] = elem(KeywordClass("match")).unit(KeywordToken("match"))
  val natMatchK: Syntax[Unit] = elem(KeywordClass("nat_match")).unit(KeywordToken("nat_match"))
  val listMatchK: Syntax[Unit] = elem(KeywordClass("list_match")).unit(KeywordToken("list_match"))
  val listMatchTypeK: Syntax[Unit] = elem(KeywordClass("List_Match")).unit(KeywordToken("List_Match"))
  val consTypeK: Syntax[Unit] = elem(KeywordClass("Cons")).unit(KeywordToken("Cons"))
  val returnsK: Syntax[Unit] = elem(KeywordClass("[returns")).unit(KeywordToken("[returns"))
  val caseK: Syntax[Unit] = elem(KeywordClass("case")).unit(KeywordToken("case"))
  val valK: Syntax[Unit] = elem(KeywordClass("val")).unit(KeywordToken("val"))
  val keepK: Syntax[Unit] = elem(KeywordClass("keep")).unit(KeywordToken("keep"))
  val errorK: Syntax[Unit] = elem(KeywordClass("error")).unit(KeywordToken("error"))
  val foldK: Syntax[Unit] = elem(KeywordClass("[fold")).unit(KeywordToken("[fold"))
  val nilK: Syntax[Unit] = elem(KeywordClass("nil")).unit(KeywordToken("nil"))
  val consK: Syntax[Unit] = elem(KeywordClass("cons")).unit(KeywordToken("cons"))
  val asK: Syntax[Unit] = elem(KeywordClass("as")).unit(KeywordToken("as"))
  val unfoldK: Syntax[Unit] = elem(KeywordClass("[unfold]")).unit(KeywordToken("[unfold]"))
  val unfoldPositiveK: Syntax[Unit] = elem(KeywordClass("[unfoldpositive]")).unit(KeywordToken("[unfoldpositive]"))
  val decreasesK: Syntax[Unit] = elem(KeywordClass("[decreases")).unit(KeywordToken("[decreases"))
  val piK: Syntax[Unit] = elem(KeywordClass("Pi")).unit(KeywordToken("Pi"))
  val sigmaK: Syntax[Unit] = elem(KeywordClass("Sigma")).unit(KeywordToken("Sigma"))
  val forallK: Syntax[Unit] = elem(KeywordClass("Forall")).unit(KeywordToken("Forall"))
  val polyForallK: Syntax[Unit] = elem(KeywordClass("PolyForall")).unit(KeywordToken("PolyForall"))
  val existsK: Syntax[Unit] = elem(KeywordClass("Exists")).unit(KeywordToken("Exists"))
  val recK: Syntax[Unit] = elem(KeywordClass("Rec")).unit(KeywordToken("Rec"))
  val typeK: Syntax[Unit] = elem(KeywordClass("type")).unit(KeywordToken("type"))

  val zeroK: Syntax[Token] = elem(KeywordClass("zero"))
  val succK: Syntax[Token] = elem(KeywordClass("succ"))
  val leftK: Syntax[Token] = elem(KeywordClass("left"))
  val rightK: Syntax[Token] = elem(KeywordClass("right"))
  val sizeK: Syntax[Token] = elem(KeywordClass("size"))


  def primitiveTypeSyntax(s: String, ty: Tree): Syntax[Tree] =
    accept(TypeClass(s))(_ => ty, {
    case `ty` => Seq(TypeToken(s))
    case _ => Seq()
  })

  val natType = primitiveTypeSyntax("Nat", NatType)
  val boolType = primitiveTypeSyntax("Bool", BoolType)
  val unitType = primitiveTypeSyntax("Unit", UnitType)
  val topType = primitiveTypeSyntax("Top", TopType)

  val primitiveType: Syntax[Tree] = natType | boolType | unitType | topType

  def opParser(op: Operator): Syntax[Token] = elem(OperatorClass(op))

  val cup = opParser(Cup)
  val plus = opParser(Plus)
  val minus = opParser(Minus)
  val mul = opParser(Mul)
  val div = opParser(Div)

  val and = opParser(And)
  val or = opParser(Or)
  val not = opParser(Not)

  val doubleEqual = opParser(Eq)
  val neq = opParser(Neq)
  val lt = opParser(Lt)
  val gt = opParser(Gt)
  val leq = opParser(Leq)
  val geq = opParser(Geq)

  lazy val parTypeExpr: Syntax[Tree] = {
    (lpar ~>~ rep1sep(typeExpr, comma) ~<~ rpar).map(Sigmas.apply, ty => Seq(Sigmas.unapply(ty).get))
  }

  lazy val piType: Syntax[Tree] = {
    (piK ~>~ lpar ~>~ termIdentifier ~<~ colon ~ typeExpr ~<~ comma ~ typeExpr ~<~ rpar).map({
      case id ~ ty1 ~ ty2 => PiType(ty1, Bind(id, ty2))
    }, {
      case PiType(ty1, Bind(id, ty2)) => Seq(id ~ ty1 ~ ty2)
      case _ => Seq()
    })
  }

  lazy val sigmaType: Syntax[Tree] = {
    (sigmaK.skip ~ lpar.skip ~ termIdentifier ~ colon.skip ~ typeExpr ~ comma.skip ~ typeExpr ~ rpar.skip).map({
      case id ~ ty1 ~ ty2 => SigmaType(ty1, Bind(id, ty2))
    }, {
      case SigmaType(ty1, Bind(id, ty2)) => Seq(id ~ ty1 ~ ty2)
      case _ => Seq()
    })
  }

  lazy val forallType: Syntax[Tree] = {
    (forallK.skip ~ lpar.skip ~ termIdentifier ~ colon.skip ~ typeExpr ~ comma.skip ~ typeExpr ~ rpar.skip).map({
      case id ~ ty1 ~ ty2 => IntersectionType(ty1, Bind(id, ty2))
    }, {
      case IntersectionType(ty1, Bind(id, ty2)) => Seq(id ~ ty1 ~ ty2)
      case _ => Seq()
    })
  }

  lazy val polyForallType: Syntax[Tree] = {
    (polyForallK.skip ~ lpar.skip ~ typeIdentifier ~ comma.skip ~ typeExpr ~ rpar.skip).map({
      case id ~ ty2 => PolyForallType(Bind(id, ty2))
    }, {
      case PolyForallType(Bind(id, ty2)) => Seq(id ~ ty2)
      case _ => Seq()
    })
  }

  lazy val existsType: Syntax[Tree] = {
    (existsK.skip ~ lpar.skip ~ termIdentifier ~ colon.skip ~ typeExpr ~ comma.skip ~ typeExpr ~ rpar.skip).map({
      case id ~ ty1 ~ ty2 => ExistsType(ty1, Bind(id, ty2))
    }, {
      case ExistsType(ty1, Bind(id, ty2)) => Seq(id ~ ty1 ~ ty2)
      case _ => Seq()
    })
  }

  lazy val recType: Syntax[Tree] = {
    (recK.skip ~ lpar.skip ~ expr ~ rpar.skip ~ lpar.skip ~ typeIdentifier ~ arrow.skip ~ typeExpr ~ rpar.skip).map({
      case y ~ alpha ~ ty => RecType(y, Bind(alpha, ty))
    }, {
      case RecType(y, Bind(alpha, ty)) => Seq(y ~ alpha ~ ty)
      case _ => Seq()
    })
  }

  lazy val refinementOrSingletonType: Syntax[Tree] =
    (lbra.skip ~ (
      (termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~
      pipe.skip ~ expr ~ rbra.skip) ||
      (lsbra.skip ~ typeExpr ~ rsbra.skip ~ expr ~ rbra.skip)
    )).map({
      case Left(x ~ ty ~ p) => RefinementType(ty, Bind(x, p))
      case Right(ty ~ t) => SingletonType(ty, t)
    }, {
      case SingletonType(ty, t) => Seq(Right(ty ~ t))
      case RefinementType(ty, Bind(x, p)) => Seq(Left(x ~ ty ~ p))
      case _ => Seq()
    })

  lazy val refinementByType: Syntax[Tree] =
    (dlbra.skip ~ termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~ pipe.skip ~ typeExpr ~ drbra.skip).map({
      case x ~ ty1 ~ ty2 => RefinementByType(ty1, Bind(x, ty2))
    }, {
      case RefinementByType(ty1, Bind(x, ty2)) => Seq(x ~ ty1 ~ ty2)
      case _ => Seq()
    })

  lazy val sumsAndUnions: Syntax[Tree] = infixLeft(simpleTypeExpr, plus | cup)({
    case (ty1, OperatorToken(`Plus`), ty2) => SumType(ty1, ty2)
    case (ty1, OperatorToken(`Cup`),  ty2) => UnionType(ty1, ty2)
  }, {
    case SumType(ty1, ty2)    => (ty1, OperatorToken(Plus), ty2)
    case UnionType(ty1, ty2)  => (ty1, OperatorToken(Cup), ty2)
  })

  lazy val arrows: Syntax[Tree] = infixRight(sumsAndUnions, arrow)({
    case (ty1, _, ty2) => PiType(ty1, Bind(Identifier.fresh("X"), ty2))
  }, {
    case PiType(ty1, Bind(id, ty2)) if !id.isFreeIn(ty2) => (ty1, OperatorToken(Plus), ty2)
  })

  def some[A](s: Syntax[A]): Syntax[Option[A]] = {
    s.map(Some(_), {
      case Some(e) => Seq(e)
      case _ => Seq()
    })
  }

  // lazy val someEqArrow: Syntax[Option[Tree]] = equal.skip ~ some(arrows)

  def withNone[A](s: Syntax[Option[A]]): Syntax[Option[A]] = epsilon(None: Option[A]) | s

  // lazy val typeOrEquality: Syntax[Tree] =
  //   (arrows ~ withNone(someEqArrow)).map({
  //     case ty ~ None => ty
  //     case ty1 ~ Some(ty2) => EqualityType(ty1, ty2)
  //   }, {
  //     case EqualityType(ty1, ty2) => Seq(ty1 ~ Some(ty2))
  //     case ty => Seq(ty ~ None)
  //   })

  lazy val equalityType: Syntax[Tree] =
    (lsbra.skip ~ expr ~ equal.skip ~ expr ~ rsbra.skip).map({
      case ty1 ~ ty2 => EqualityType(ty1, ty2)
    }, {
      case EqualityType(ty1, ty2) => Seq(ty1 ~ ty2)
      case _ => Seq()
    })

  lazy val simpleTypeExpr: Syntax[Tree] =
    primitiveType | parTypeExpr | recType |
    refinementOrSingletonType | refinementByType |
    macroTypeInst | equalityType |
    piType | sigmaType | forallType | polyForallType |
    existsType | listMatchType | consType

  lazy val typeExpr: Syntax[Tree] = recursive { arrows }

  val boolean: Syntax[Tree] = accept(BooleanClass)({
    case BooleanToken(value) => BooleanLiteral(value)
  }, {
    case BooleanLiteral(value) => Seq(BooleanToken(value))
    case _ => Seq()
  })

  val number: Syntax[Tree] = accept(NumberClass)({
    case NumberToken(value) => NatLiteral(value)
  }, {
    case NatLiteral(value) => Seq(NumberToken(value))
    case _ => Seq()
  })

  def builtinIdentifier(s: String): Syntax[Identifier] = {
    elem(KeywordClass(s)).map({
      case t => Identifier(0, s).setPos(t)
    }, {
      case Identifier(0, s) => Seq(KeywordToken(s))
      case _ => Seq()
    })
  }

  lazy val userIdentifier: Syntax[Identifier] = accept(TermIdentifierClass)({
    case t@TermIdentifierToken(content) => Identifier(0, content).setPos(t)
  }, {
    case Identifier(id, name) if (!name.isEmpty && name(0).isLower) =>
      if (rc.config.printUniqueIds)
        Seq(TermIdentifierToken(s"$name#$id"))
      else
        Seq(TermIdentifierToken(name))
    case _ => Seq()
  })

  lazy val termIdentifier: Syntax[Identifier] =
    userIdentifier |
    BuiltInIdentifiers.builtInIdentifiers.map(s => builtinIdentifier(s)).reduce(_ | _)

  lazy val userTypeIdentifier: Syntax[Identifier] = accept(TypeIdentifierClass)({
    case t@TypeIdentifierToken(content) => Identifier(0, content).setPos(t)
  }, {
    case Identifier(id, name) if (!name.isEmpty && name(0).isUpper) =>
      if (rc.config.printUniqueIds)
        Seq(TypeIdentifierToken(s"$name#$id"))
      else
        Seq(TypeIdentifierToken(name))
    case _ => Seq()
  })

  lazy val typeIdentifier =
    userTypeIdentifier |
    BuiltInIdentifiers.builtInTypeIdentifiers.map(s => builtinIdentifier(s)).reduce(_ | _)

  lazy val termVariable: Syntax[Tree] = termIdentifier.map(Var(_), {
    case Var(id) => Seq(id)
    case _ => Seq()
  })

  lazy val unit: Syntax[Tree] = accept(UnitClass)({ case _ => UnitLiteral }, {
    case UnitLiteral => Seq(UnitToken)
    case _ => Seq()
  })

  lazy val literal: Syntax[Tree] = termVariable | number | boolean | unit

  lazy val untypedArgument: Syntax[DefArgument] = {
    termIdentifier.map({
      case id => UntypedArgument(id)
    }, {
      case UntypedArgument(id) => Seq(id)
      case _ => Seq()
    })
  }

  lazy val typedArgument: Syntax[DefArgument] = {
    (lpar.skip ~ termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~ rpar.skip).map({
      case id ~ ty => TypedArgument(id, ty)
    }, {
      case TypedArgument(id, ty) => Seq(id ~ ty)
      case _ => Seq()
    })
  }

  lazy val typeArgument: Syntax[DefArgument] =
    (lsbra.skip ~ typeIdentifier ~ rsbra.skip).map({
      case id => TypeArgument(id): DefArgument
    }, {
      case TypeArgument(id) => Seq(id)
      case _ => Seq()
    })

  lazy val ghostArgument: Syntax[DefArgument] = {
    (dlsbra.skip ~ termIdentifier ~ colon.skip ~ typeExpr ~ drsbra.skip).map({
      case id ~ ty => ForallArgument(id, ty): DefArgument
    }, {
      case ForallArgument(id, ty) => Seq(id ~ ty)
      case _ => Seq()
    })
  }

  lazy val argument: Syntax[DefArgument] = untypedArgument | typedArgument | typeArgument | ghostArgument

  lazy val defFunction: Syntax[Tree] =
    (funK.skip ~ termIdentifier ~ many(argument) ~ opt(retTypeP) ~ equal.skip ~ lbraBlock.skip ~ opt(measureP) ~
    expr ~ rbraBlock2.skip ~ opt(expr)).map({
      case f ~ args ~ optRet ~ optMeasure ~ e1 ~ e2 =>
        val ids = args.map(_.id)
        val followingExpr = e2.getOrElse(Var(f))
        DefFunction(
          args,
          optRet.map(ret => Binds(ids, ret)),
          optMeasure.map(measure => Binds(ids, measure)),
          Binds(ids, Bind(f, e1)),
          Binds(ids, Bind(f, followingExpr))
        )
      case _ => sys.error("Unreachable")
    }, {
      case DefFunction(args, optRet, optMeasure, e1, Binds(ids, body)) =>
        Seq(
          ids.last ~
          args ~
          optRet.map(Binds.remove) ~
          optMeasure.map(Binds.remove) ~
          Binds.remove(e1) ~
          Some(body)
        )
      case _ => Seq()
    })

  lazy val retTypeP: Syntax[Tree] = {
    returnsK ~>~ typeExpr ~<~ rsbra
  }

  lazy val measureP: Syntax[Tree] = {
    decreasesK ~>~ expr ~<~ rsbraNewLine
  }

  lazy val lambda: Syntax[Tree] =
    (funOfK.skip ~ many(argument) ~ equal.skip ~ bracketExpr).map({
      case args ~ e => Abstractions(args, e)
    }, {
      case Abstractions(args, e) => Seq(args ~ e)
      case _ => Seq()
    })

  lazy val keep: Syntax[Tree] =
    (keepK.skip ~ bracketExpr).map({
      case e => Lambda(Some(UnitType), Bind(Identifier(0, "u"), e))
    }, {
      case Lambda(Some(UnitType), Bind(id, e)) if !id.isFreeIn(e) => Seq(e)
      case _ => Seq()
    })

  lazy val string: Syntax[String] = accept(StringClass)({
    case StringToken(content) => content
    case _ => sys.error("Unreachable")
  }, {
    s => Seq(StringToken(s))
  })


  lazy val error: Syntax[Tree] =
    (errorK.skip ~ opt(lsbra.skip ~ typeExpr ~ rsbra.skip) ~ lpar.skip ~ string ~ rpar.skip).map({
      case optTy ~ s => Error(s, optTy)
    }, {
      case Error(s, optTy) => Seq(optTy ~ s)
      case _ => Seq()
    })

  lazy val fixpoint: Syntax[Tree] =
    (fixK.skip ~ opt(lsbra.skip ~ termIdentifier ~ rsbra.skip ~ lsbra.skip ~ typeExpr ~ rsbra.skip) ~
    lpar.skip ~ termIdentifier ~ arrow.skip ~ expr ~ rpar.skip).map({
      case None ~ x ~ e =>
        Fix(None, Bind(Identifier.fresh("n"), Bind(x, e)))
      case Some(n ~ tp) ~ x ~ e =>
        Fix(Some(Bind(n, tp)), Bind(n, Bind(x, e)))
      case _ =>
        sys.error("Unreachable")
    }, {
      case Fix(None, Bind(id, Bind(x, e))) =>
        assert(!id.isFreeIn(e))
        Seq(None ~ x ~ e)
      case Fix(Some(Bind(n1, tp)), Bind(n2, Bind(x, e))) =>
        Seq(Some(n1 ~ tp) ~ x ~ e.replace(n2, n1)(rc))
      case _ => Seq()
    })

  // `fixD(x [T] => t, td)`
  lazy val fixpointWithDefault: Syntax[Tree] =
    (fixDK.skip ~ lpar.skip ~ termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~
      arrow.skip ~ expr ~ comma.skip ~ expr ~ rpar.skip).map({
      case x ~ tp ~ e ~ ed =>
        FixWithDefault(tp, Bind(x, e), ed)
      case _ =>
        sys.error("Unreachable")
    }, {
      case FixWithDefault(tp, Bind(x, e), ed) =>
        Seq(x ~ tp ~ e ~ ed)
      case _ => Seq()
    })

  lazy val fold: Syntax[Tree] =
    (foldK.skip ~ asK.skip ~ typeExpr ~ rsbra.skip ~
    lpar.skip ~ expr ~ rpar.skip).map({
      case ty ~ e  => Fold(ty, e)
      case _ => sys.error("Unreachable")
    }, {
      case Fold(ty, e) => Seq(ty ~ e)
      case _ => Seq()
    })

  lazy val unfoldIn: Syntax[Tree] =
    (unfoldK.skip ~ valK.skip ~ termIdentifier ~ equal.skip ~ expr ~ semicolon.skip ~
     expr).map({
      case x ~ e1 ~ e2 => Unfold(e1, Bind(x, e2))
      case _ => sys.error("Unreachable")
    }, {
      case Unfold(e1, Bind(x, e2)) => Seq(x ~ e1 ~ e2)
      case _ => Seq()
    })

  lazy val unfoldPositiveIn: Syntax[Tree] =
    (unfoldPositiveK.skip ~ valK.skip ~ termIdentifier ~ equal.skip ~ expr ~ semicolon.skip ~
     expr).map({
      case x ~ e1 ~ e2 => UnfoldPositive(e1, Bind(x, e2))
      case _ => sys.error("Unreachable")
    }, {
      case UnfoldPositive(e1, Bind(x, e2)) => Seq(x ~ e1 ~ e2)
      case _ => Seq()
    })

  lazy val letIn: Syntax[Tree] =
     (valK.skip ~ termIdentifier ~ opt(lsbra.skip ~ typeExpr ~ rsbra.skip) ~ equal.skip ~
      expr ~ semicolon.skip ~ expr).map({
      case x ~ optTy ~ e ~ e2 => LetIn(optTy, e, Bind(x, e2))
      case _ => sys.error("Unreachable")
    }, {
      case LetIn(optTy, e, Bind(x, e2)) => Seq(x ~ optTy ~ e ~ e2)
      case _ => Seq()
    })

  lazy val parExpr: Syntax[Tree] =
    (lpar ~>~ repsep(expr, comma) ~<~ rpar).map(Pairs(_),
      e => Seq(Pairs.unapply(e).get)
    )

  lazy val sBracketAppArg: Syntax[AppArgument] = {
    (lsbra.skip ~ typeExpr ~ rsbra.skip).map({
      case e => TypeAppArg(e)
    }, {
      case TypeAppArg(e) => Seq(e)
      case _ => Seq()
    })
  }

  lazy val bracketAppArg: Syntax[AppArgument] = {
    (dlsbra.skip ~ expr ~ drsbra.skip).map({
      case e => ErasableAppArg(e)
    }, {
      case ErasableAppArg(e) => Seq(e)
      case _ => Seq()
    })
  }

  lazy val parAppArg: Syntax[AppArgument] = {
    simpleExpr.map({
      case e => AppArg(e)
    }, {
      case AppArg(e) => Seq(e)
      case _ => Seq()
    })
  }

  lazy val appArg: Syntax[AppArgument] = parAppArg | bracketAppArg | sBracketAppArg

  lazy val application: Syntax[Tree] = {
    (simpleExpr ~ many(appArg)).map({
      case f ~ args => Applications(f, args)
    }, {
      case LNil()       => Seq(Var(Identifier(0, "nil")) ~ Seq())
      case LCons(x, xs) => Seq(Var(Identifier(0, "cons")) ~ Seq(AppArg(x), AppArg(xs)))
      case LeftTree(t)  => Seq(Var(Identifier(0, "left"))   ~ Seq(AppArg(t)))
      case RightTree(t) => Seq(Var(Identifier(0, "right"))  ~ Seq(AppArg(t)))
      case Size(t)      => Seq(Var(Identifier(0, "size"))   ~ Seq(AppArg(t)))
      case First(t)     => Seq(Var(Identifier(0, "first"))  ~ Seq(AppArg(t)))
      case Second(t)    => Seq(Var(Identifier(0, "second")) ~ Seq(AppArg(t)))
      case Choose(ty)   => Seq(Var(Identifier(0, "choose")) ~ Seq(TypeAppArg(ty)))
      case Applications(f, args) => Seq(f ~ args)
      case _ => Seq()
    })
  }

  lazy val macroTermArg: Syntax[(Boolean, Tree)] =
    simpleExpr.map((true, _), {
      case (true, e) => Seq(e)
      case _ => Seq()
    })

  lazy val macroTypeArg: Syntax[(Boolean, Tree)] =
    (lsbra.skip ~ typeExpr ~ rsbra.skip).map((false, _), {
      case (false, e) => Seq(e)
      case _ => Seq()
    })

  lazy val macroTypeInst: Syntax[Tree] =
    (typeIdentifier ~ many(macroTermArg | macroTypeArg)).map({
      case id ~ Nil => Var(id)
      case id ~ args => MacroTypeInst(Var(id), args)
    }, {
      case Var(id) => Seq(id ~ Nil)
      case t if t == typechecker.ScalaDepSugar.LList => Seq(Identifier(0, "List") ~ Nil)
      case MacroTypeInst(Var(id), args) => Seq(id ~ args)
      case _ => Seq()
    })

  lazy val eitherMatch: Syntax[Tree] =
    (matchK.skip ~ expr ~ lbra.skip ~
      caseK.skip ~ leftK.unit(KeywordToken("left")).skip ~ termIdentifier ~ arrow.skip ~ optBracketExpr ~
      caseK.skip ~ rightK.unit(KeywordToken("right")).skip ~ termIdentifier ~ arrow.skip ~ optBracketExpr ~
    rbra.skip
    ).map({
      case (e ~ id1 ~ e1 ~ id2 ~ e2) => EitherMatch(e, Bind(id1, e1), Bind(id2, e2))
      case _ => sys.error("Unreachable")
    }, {
      case EitherMatch(e, Bind(id1, e1), Bind(id2, e2)) => Seq(e ~ id1 ~ e1 ~ id2 ~ e2)
      case _ => Seq()
    })

  lazy val natMatch: Syntax[Tree] =
    (natMatchK.skip ~ expr ~ lbra.skip ~
      caseK.skip ~ zeroK.unit(KeywordToken("zero")).skip ~ arrow.skip ~ optBracketExpr ~
      caseK.skip ~ succK.unit(KeywordToken("succ")).skip ~ termIdentifier ~ arrow.skip ~ optBracketExpr ~
    rbra.skip
    ).map({
      case (e ~ e1 ~ id2 ~ e2) => NatMatch(e, e1, Bind(id2, e2))
      case _ => sys.error("Unreachable")
    }, {
      case NatMatch(e, e1, Bind(id2, e2)) => Seq(e ~ e1 ~ id2 ~ e2)
      case _ => Seq()
    })

  lazy val listMatch: Syntax[Tree] =
    (listMatchK.skip ~ expr ~ lbra.skip ~
      caseK.skip ~ nilK.unit(KeywordToken("nil")).skip ~ arrow.skip ~ optBracketExpr ~
      caseK.skip ~ consK.unit(KeywordToken("cons")).skip ~ termIdentifier ~ termIdentifier ~
        arrow.skip ~ optBracketExpr ~
    rbra.skip
    ).map({
      case (e ~ e1 ~ idHead ~ idTail ~ e2) => ListMatch(e, e1, Bind(idHead, Bind(idTail, e2)))
      case _ => sys.error("Unreachable")
    }, {
      case ListMatch(e, e1, Bind(idHead, Bind(idTail, e2))) => Seq(e ~ e1 ~ idHead ~ idTail ~ e2)
      case _ => Seq()
    })

  lazy val listMatchType: Syntax[Tree] =
    (listMatchTypeK.skip ~ typeExpr ~ lbra.skip ~
      caseK.skip ~ nilK.unit(KeywordToken("nil")).skip ~ arrow.skip ~ typeExpr ~
      caseK.skip ~ consK.unit(KeywordToken("cons")).skip ~ termIdentifier ~ termIdentifier ~
        arrow.skip ~ typeExpr ~
    rbra.skip
    ).map({
      case (ty ~ ty1 ~ idHead ~ idTail ~ ty2) =>
        ListMatchType(ty, ty1, Bind(idHead, Bind(idTail, ty2)))
      case _ => sys.error("Unreachable")
    }, {
      case ListMatchType(ty, ty1, Bind(idHead, Bind(idTail, ty2))) =>
        Seq(ty ~ ty1 ~ idHead ~ idTail ~ ty2)
      case _ => Seq()
    })

  lazy val consType: Syntax[Tree] =
    (consTypeK.skip ~ lsbra.skip ~ typeExpr ~ comma.skip ~ typeExpr ~ rsbra.skip).map({
      case (tyHead ~ tyTail) => LConsType(tyHead, tyTail)
      case _ => sys.error("Unreachable")
    }, {
      case LConsType(tyHead, tyTail) => Seq(tyHead ~ tyTail)
      case _ => Seq()
    })

  lazy val notApplication: Syntax[Tree] = prefixes(not, application)({
      case (_, e) => Primitive(Not, List(e))
      case _ => sys.error("Unreachable")
    }, {
      case Primitive(not, List(e)) => (OperatorToken(Not), e)
    })

  lazy val mulDivAnd: Syntax[Tree] = infixLeft(notApplication, mul | div | and)({
    case (x, OperatorToken(op), y) => Primitive(op, List(x,y))
    case _ => sys.error("Unreachable")
  }, {
    case Primitive(op, x ::  y ::  Nil)
      if op == Mul || op == Div || op == And =>

      (x, OperatorToken(op), y)
  })

  lazy val plusMinusOr: Syntax[Tree] = infixLeft(mulDivAnd, plus | minus | or)({
    case (x, OperatorToken(op), y) => Primitive(op, List(x,y))
    case _ => sys.error("Unreachable")
  }, {
    case Primitive(op, x ::  y ::  Nil)
      if op == Plus || op == Minus || op == Or =>

      (x, OperatorToken(op), y)
  })

  lazy val ltGtLeqGeq: Syntax[Tree] = infixLeft(plusMinusOr, lt | gt | leq | geq)({
    case (x, OperatorToken(op), y) => Primitive(op, List(x,y))
    case _ => sys.error("Unreachable")
  }, {
    case Primitive(op, x ::  y ::  Nil)
      if op == Lt || op == Gt || op == Leq || op == Geq => (x, OperatorToken(op), y)
  })

  lazy val termOrEquality: Syntax[Tree] =
    (ltGtLeqGeq ~ withNone(doubleEqual.unit(OperatorToken(Eq)).skip ~ some(ltGtLeqGeq))).map({
      case ty ~ None => ty
      case ty1 ~ Some(ty2) => Primitive(Eq, List(ty1, ty2))
    }, {
      case Primitive(Eq, x ::  y ::  Nil) => Seq(x ~ Some(y))
      case e => Seq(e ~ None)
    })

  lazy val condition: Syntax[Tree] = {
    (ifK.skip ~ lpar.skip ~ expr ~ rpar.skip ~ bracketExpr ~ elseK.skip ~ bracketExpr).map({
      case cond ~ e1 ~ e2 => IfThenElse(cond, e1, e2)
      case _ => sys.error("Unreachable")
    }, {
      case IfThenElse(cond, e1, e2) => Seq(cond ~ e1 ~ e2)
      case _ => Seq()
    })
  }

  lazy val optBracketExpr: Syntax[Tree] = expr | bracketExpr

  lazy val bracketExpr: Syntax[Tree] = lbraBlock.skip ~ expr ~ rbraBlock.skip

  lazy val simpleExpr: Syntax[Tree] =
    fixpointWithDefault | literal | parExpr | fixpoint |
    lambda | keep | error | fold

  lazy val macroTypeDeclaration: Syntax[Tree] = {
    (lsbra.skip ~ typeK.skip ~ typeIdentifier ~
      many((lpar.skip ~ termIdentifier ~ rpar.skip) |
           (lsbra.skip ~ typeIdentifier ~ rsbra.skip)) ~
      equal.skip ~ typeExpr ~ rsbraNewLines.skip ~ expr).map({
      case id ~ ids ~ ty ~ rest =>
        MacroTypeDecl(Binds(ids, ty), Bind(id, rest))
      case _ =>
        sys.error("Unreachable")
    }, {
      case MacroTypeDecl(Binds(ids, ty), Bind(id, rest)) =>
        Seq(id ~ ids ~ ty ~ rest)
      case _ => Seq()
    })
  }

  lazy val expr: Syntax[Tree] = recursive {
    termOrEquality | condition | eitherMatch |
    natMatch | listMatch |
    letIn | unfoldIn | unfoldPositiveIn |
    defFunction | macroTypeDeclaration
  }

  val exprParser = LL1(expr)

  def apply(it: Iterator[Token]): LL1.ParseResult[Tree] = exprParser(it)
}
