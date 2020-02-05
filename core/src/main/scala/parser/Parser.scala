package core
package parser

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

import core.trees._

import util.Utils._

sealed abstract class Token extends Positioned

case object AssignationToken extends Token

case class KeyWordToken(value: String) extends Token
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

object ScalaLexer extends Lexers with CharRegExps {
  type Token = parser.Token
  type Position = (Int, Int)

  val blank = many { elem(c => c == '\n' || c == ' ') }

  val lexer = Lexer(
    // Operators
    oneOf("-+/*!<>") | word("&&") |  word("||") |
    word("==") | word("!=") | word("<=") | word(">=")
    |> { (cs, r) => OperatorToken(Operator.fromString(cs.mkString).get).setPos(r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => AssignationToken.setPos(r) },

    // Keywords
    (elem('{') ~ blank ~ word("case")) |
    (elem('[') ~ blank ~ word("returns")) |
    (elem('[') ~ blank ~ word("fold")) |
    (elem('[') ~ blank ~ word("decreases")) |
    (elem('[') ~ blank ~ word("unfold") ~ blank ~ elem(']')) |
    (elem('[') ~ blank ~ word("unfold") ~ blank ~ word("positive") ~ elem(']')) |
    word("as") | word("fun of") | word("keep") |
    word("if") | word("else") | word("case") | word("match") |
    word("fix") | word("fun") | word("val") |
    word("Error") |
    word("left") | word("right") | word("size") |
    word("Rec") | word("Pi") | word("Sigma") |
    word("Forall") | word("PolyForall") |
    word("Lambda") |
    word("type")
      |> { (cs, r) => KeyWordToken(cs.mkString.replaceAll("""[ \n]""", "")).setPos(r) },

    // Compound separator
    word("[|") | word("|]")
      |> { (cs, r) => SeparatorToken(cs.mkString).setPos(r) },

    // Separator
    oneOf("{},|().:;[]") | word("=>")
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
case object AssignationClass extends TokenClass
case class KeyWordClass(value: String) extends TokenClass
case class TypeClass(value: String) extends TokenClass

object ScalaParser extends Syntaxes with Operators with ll1.Parsing with ll1.Debug {

  type Token = parser.Token
  type Kind = parser.TokenClass

  import Implicits._

  var id = 0

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value) => SeparatorClass(value)
    case BooleanToken(value) => BooleanClass
    case NumberToken(value) => NumberClass
    case TypeIdentifierToken(content) => TypeIdentifierClass
    case TermIdentifierToken(content) => TermIdentifierClass
    case OperatorToken(op) => OperatorClass(op)
    case AssignationToken => AssignationClass
    case KeyWordToken(value) => KeyWordClass(value)
    case UnitToken => UnitClass
    case TypeToken(content) => TypeClass(content)
    case StringToken(content) => StringClass
    case _ => NoClass
  }

  def newId: Int = {
    id = id + 1
    id
  }

  val assignation: Syntax[Token] = elem(AssignationClass)
  val dlbra: Syntax[Token] = elem(SeparatorClass("[|"))
  val drbra: Syntax[Token] = elem(SeparatorClass("|]"))
  val lpar: Syntax[Token] = elem(SeparatorClass("("))
  val rpar: Syntax[Token] = elem(SeparatorClass(")"))
  val lbra: Syntax[Token] = elem(SeparatorClass("{"))
  val rbra: Syntax[Token] = elem(SeparatorClass("}"))
  val lsbra: Syntax[Token] = elem(SeparatorClass("["))
  val rsbra: Syntax[Token] = elem(SeparatorClass("]"))
  val comma: Syntax[Token] = elem(SeparatorClass(","))
  val pipe: Syntax[Token] = elem(SeparatorClass("|"))
  val colon: Syntax[Token] = elem(SeparatorClass(":"))
  val semicolon: Syntax[Token] = elem(SeparatorClass(";"))
  val appK: Syntax[Token] = elem(SeparatorClass("\\"))
  val tupleK: Syntax[Token] = elem(SeparatorClass("\\("))
  val dot: Syntax[Token] = elem(SeparatorClass("."))
  val arrow: Syntax[Token] = elem(SeparatorClass("=>"))
  val ifK: Syntax[Token] = elem(KeyWordClass("if"))
  val elseK: Syntax[Token] = elem(KeyWordClass("else"))
  val fixK: Syntax[Token] = elem(KeyWordClass("fix"))
  val funK: Syntax[Token] = elem(KeyWordClass("fun"))
  val funOfK: Syntax[Token] = elem(KeyWordClass("funof"))
  val sizeK: Syntax[Token] = elem(KeyWordClass("size"))
  val leftK: Syntax[Token] = elem(KeyWordClass("left"))
  val rightK: Syntax[Token] = elem(KeyWordClass("right"))
  val matchK: Syntax[Token] = elem(KeyWordClass("match"))
  val returnsK: Syntax[Token] = elem(KeyWordClass("[returns"))
  val caseK: Syntax[Token] = elem(KeyWordClass("case"))
  val lbracase: Syntax[Token] = elem(KeyWordClass("{case"))
  val valK: Syntax[Token] = elem(KeyWordClass("val"))
  val keepK: Syntax[Token] = elem(KeyWordClass("keep"))
  val errorK: Syntax[Token] = elem(KeyWordClass("Error"))
  val foldK: Syntax[Token] = elem(KeyWordClass("[fold"))
  val asK: Syntax[Token] = elem(KeyWordClass("as"))
  val unfoldK: Syntax[Token] = elem(KeyWordClass("[unfold]"))
  val unfoldPositiveK: Syntax[Token] = elem(KeyWordClass("[unfoldpositive]"))
  val decreasesK: Syntax[Token] = elem(KeyWordClass("[decreases"))
  val piK: Syntax[Token] = elem(KeyWordClass("Pi"))
  val sigmaK: Syntax[Token] = elem(KeyWordClass("Sigma"))
  val forallK: Syntax[Token] = elem(KeyWordClass("Forall"))
  val polyForallK: Syntax[Token] = elem(KeyWordClass("PolyForall"))
  val recK: Syntax[Token] = elem(KeyWordClass("Rec"))
  val lambdaK: Syntax[Token] = elem(KeyWordClass("Lambda"))
  val typeK: Syntax[Token] = elem(KeyWordClass("type"))

  val natType: Syntax[Tree] = accept(TypeClass("Nat")) { case _ => NatType }
  val boolType: Syntax[Tree] = accept(TypeClass("Bool")) { case _ => BoolType }
  val unitType: Syntax[Tree] = accept(TypeClass("Unit")) { case _ => UnitType }
  val topType: Syntax[Tree] = accept(TypeClass("Top")) { case _ => TopType }

  val literalType: Syntax[Tree] = natType | boolType | unitType | topType

  def opParser(op: Operator): Syntax[Token] = elem(OperatorClass(op))

  lazy val parTypeExpr: Syntax[Tree] = {
    (lpar ~ rep1sep(typeExpr, comma.unit()) ~ rpar).map {
      case _ ~ l ~ _ =>
        if (l.size == 1) l.head
        else {
          val h = l.reverse.head
          val r = l.reverse.tail.reverse
          r.foldRight(h) { case (e, acc) =>
            SigmaType(e, Bind(Identifier(newId, "_S"), acc)).setPos(e, acc)
          }
        }
    }
  }

  lazy val bPiType: Syntax[Tree] = {
    (piK ~ lpar ~ termIdentifier ~ colon ~ typeExpr ~ comma ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ id ~ _ ~ ty1 ~ _ ~ ty2 ~ _ => PiType(ty1, Bind(id, ty2))
    }
  }

  lazy val bSigmaType: Syntax[Tree] = {
    (sigmaK ~ lpar ~ termIdentifier ~ colon ~ typeExpr ~ comma ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ id ~ _ ~ ty1 ~ _ ~ ty2 ~ _ => SigmaType(ty1, Bind(id, ty2))
    }
  }

  lazy val bForallType: Syntax[Tree] = {
    (forallK.skip ~ lpar.skip ~ termIdentifier ~ colon.skip ~ typeExpr ~ comma.skip ~ typeExpr ~ rpar.skip).map {
      case id ~ ty1 ~ ty2 => IntersectionType(ty1, Bind(id, ty2))
    }
  }

  lazy val polyForallType: Syntax[Tree] = {
    (polyForallK.skip ~ lpar.skip ~ typeIdentifier ~ comma.skip ~ typeExpr ~ rpar.skip).map {
      case id ~ ty2 => PolyForallType(Bind(id, ty2))
    }
  }

  lazy val recType: Syntax[Tree] = {
    (recK.skip ~ lpar.skip ~ expr ~ rpar.skip ~ lpar.skip ~ typeIdentifier ~ arrow.skip ~ typeExpr ~ rpar.skip).map {
      case y ~ alpha ~ ty => RecType(y, Bind(alpha, ty))
    }
  }

  lazy val refinementType: Syntax[Tree] = {
    (lbra.skip ~ termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~ pipe.skip ~ expr ~ rbra.skip).map {
      case x ~ ty ~ p => RefinementType(ty, Bind(x, p))
    }
  }

  lazy val operatorType: Syntax[Tree] = {
    operators(simpleTypeExpr)(
      plus is LeftAssociative,
      arrow is RightAssociative,
      eq is LeftAssociative
    )({
      case (ty1, t @ SeparatorToken("=>"), ty2) => PiType(ty1, Bind(Identifier(newId, "_X"), ty2))
      case (ty1, t @ OperatorToken(Plus), ty2) => SumType(ty1, ty2)
      case (ty1, t @ OperatorToken(Eq), ty2) => EqualityType(ty1, ty2)
    }, {
      case PiType(ty1, Bind(_, ty2)) => (ty1, SeparatorToken("=>"), ty2)
      case SumType(ty1, ty2) => (ty1, OperatorToken(Plus), ty2)
      case EqualityType(ty1, ty2) => (ty1, OperatorToken(Eq), ty2)
    })
  }

  lazy val simpleTypeExpr: Syntax[Tree] =
    literalType | parTypeExpr | recType | refinementType |
    macroTypeInst |
    bPiType | bSigmaType | bForallType | polyForallType

  lazy val typeExpr: Syntax[Tree] = recursive {
    operatorType
  }

  val boolean: Syntax[Tree] = accept(BooleanClass) { case BooleanToken(value) => BooleanLiteral(value) }
  val number: Syntax[Tree] = accept(NumberClass) { case NumberToken(value) => NatLiteral(value) }

  val termIdentifier: Syntax[Identifier] = accept(TermIdentifierClass) {
    case t@TermIdentifierToken(content) => Identifier(0, content).setPos(t)
  } |
    leftK.map { case t => Identifier(0, "left").setPos(t) } |
    rightK.map { case t => Identifier(0, "right").setPos(t) } |
    sizeK.map { case t => Identifier(0, "size").setPos(t) }


  val typeIdentifier: Syntax[Identifier] = accept(TypeIdentifierClass) {
    case t@TypeIdentifierToken(content) => Identifier(0, content).setPos(t)
  }
  val termVariable: Syntax[Tree] = termIdentifier.map(Var(_))
  val typeVariable: Syntax[Tree] = typeIdentifier.map(Var(_))

  val unit: Syntax[Tree] = accept(UnitClass) { case _ => UnitLiteral }

  val literal: Syntax[Tree] = termVariable | number | boolean | unit

  val plus = opParser(Plus)
  val minus = opParser(Minus)
  val mul = opParser(Mul)
  val div = opParser(Div)

  val and = opParser(And)
  val or = opParser(Or)
  val not = opParser(Not)

  val eq = opParser(Eq)
  val neq = opParser(Neq)
  val lt = opParser(Lt)
  val gt = opParser(Gt)
  val lteq = opParser(Lteq)
  val gteq = opParser(Gteq)

  lazy val lambdaAbs: Syntax[Tree] = {
    (lambdaK ~ termIdentifier ~ arrow ~ bracketExpr).map {
      case _ ~ x ~ _ ~ e => Abs(Bind(x, e))
    }
  }

  sealed abstract class DefArgument {
    def toAppArgument(): AppArgument
  }

  case class TypeArgument(id: Identifier) extends DefArgument {
    def toAppArgument(): AppArgument = TypeAppArg(Var(id))
  }

  case class ForallArgument(id: Identifier, ty: Tree) extends DefArgument {
    def toAppArgument(): AppArgument = ErasableAppArg(Var(id))
  }

  case class PiArgument(id: Identifier, ty: Tree) extends DefArgument {
    def toAppArgument(): AppArgument = TermAppArg(Var(id))
  }

  lazy val normalArgument: Syntax[DefArgument] = {
    (lpar.skip ~ termIdentifier ~ lsbra.skip ~ typeExpr ~ rsbra.skip ~ rpar.skip).map {
      case id ~ ty => PiArgument(id, ty)
    }
  }

  lazy val typeArgument: Syntax[DefArgument] =
    (lsbra.skip ~ typeIdentifier ~ rsbra.skip).map { case id => TypeArgument(id): DefArgument }

  lazy val ghostArgument: Syntax[DefArgument] = {
    (dlbra.skip ~ termIdentifier ~ colon ~ typeExpr ~ drbra.skip).map {
      case id ~ _ ~ ty => ForallArgument(id, ty): DefArgument
    }
  }

  lazy val argument: Syntax[DefArgument] = normalArgument | typeArgument | ghostArgument

  def createFun(args: Seq[DefArgument], retType: Option[Tree], body: Tree, f: Identifier): (Tree, Option[Tree]) = {
    val (fun, funType) = args.foldRight((body, retType.getOrElse(UnitType))) {
      case (arg, (accTree, accType)) =>
        arg match {
          case TypeArgument(id)   => (Abs(Bind(id, accTree)), PolyForallType(Bind(id, accType)))
          case ForallArgument(id, ty) => (ErasableLambda(ty, Bind(id, accTree)), IntersectionType(ty, (Bind(id, accType))))
          case PiArgument(id, ty) => (Lambda(Some(ty), Bind(id, accTree)), PiType(ty, Bind(id, accType)))
        }
    }
    if (retType.isEmpty) (fun, None)
    else (fun, Some(funType))
  }

  lazy val defFunction: Syntax[Tree] =
    (funK.skip ~ termIdentifier ~ many1(argument) ~ opt(retTypeP) ~ assignation.skip ~ lbra.skip ~ opt(measureP) ~
    expr ~ rbra.skip ~ opt(expr)).map {
      case f ~ args ~ retType ~ measure ~ e1 ~ e2 =>
        val followingExpr = e2.getOrElse(Var(f))
        if (f.isFreeIn(e1) && measure.isEmpty) {
          throw new java.lang.Exception(s"Recursive function $f needs a Decreases clause.")
        }
        (measure, retType) match {
          case (Some(_), None) =>
            throw new java.lang.Exception(s"Recursive function $f a needs return type.")
          case (None, None) =>
            val (fun, _) = createFun(args, None, e1, f)
            LetIn(None, fun, Bind(f, followingExpr))
          case (None, Some(ty)) =>
            val (fun, funType) = createFun(args, Some(ty), e1, f)
            LetIn(Some(funType.get), fun, Bind(f, followingExpr))
          case (Some(measure), Some(ty)) =>
            val n = freshIdentifier("_n")
            val expr = e1.replace(f,
              Inst(App(Var(f), UnitLiteral),
                Primitive(Minus, List(Var(n), NatLiteral(1)))
              )
            )
            val refinedArgs = mapFirst(args.reverse, { (arg: DefArgument) => arg match {
              case ForallArgument(id, ty) =>
                Some(ForallArgument(id, RefinementType(ty, Bind(id, Primitive(Lteq, List(measure, Var(n)))))))
              case PiArgument(id, ty) =>
                Some(PiArgument(id, RefinementType(ty, Bind(id, Primitive(Lteq, List(measure, Var(n)))))))
              case _ =>
                None
            }}).getOrElse(
              throw new java.lang.Exception(s"Recursive function $f must have at least one non-type argument")
            ).reverse
            val (fun, funTy) = createFun(refinedArgs, Some(ty), expr, f)
            val fix = Fix(Some(Bind(n, funTy.get)), Bind(n, Bind(f, fun)))

            val instBody = createApp(
              args.map(_.toAppArgument),
              Inst(Var(f), Primitive(Plus, List(measure, NatLiteral(1))))
            )
            val (instFun, _) = createFun(args, Some(ty), instBody, f)
            LetIn(None, fix, Bind(f,
              LetIn(None, instFun, Bind(f,
                followingExpr)
              )
            ))
        }
    }

  lazy val retTypeP: Syntax[Tree] = {
    returnsK ~>~ typeExpr ~<~ rsbra
  }

  lazy val measureP: Syntax[Tree] = {
    decreasesK ~>~ expr ~<~ rsbra
  }

  lazy val function: Syntax[Tree] = {
    (funOfK.skip ~ many(argument) ~ assignation.skip ~ bracketExpr).map {
      case args ~ e => createFun(args, None, e, Identifier(0, "__"))._1
    }
  }

  lazy val keep: Syntax[Tree] = {
    (keepK.skip ~ bracketExpr).map {
      case e =>
        Lambda(Some(UnitType), Bind(Identifier(0, "__"), e))
    }
  }

  lazy val string: Syntax[String] = accept(StringClass) { case StringToken(content) => content }

  lazy val error: Syntax[Tree] = {
    (errorK.skip ~ opt(lsbra.skip ~ typeExpr ~ rsbra.skip) ~ lpar.skip ~ string ~ rpar.skip).map {
      case optTy ~ s => Error(s, optTy)
    }
  }

  lazy val fixpoint: Syntax[Tree] =
    (fixK.skip ~ opt(lsbra ~ termVariable ~ arrow ~ typeExpr ~ rsbra) ~
    lpar.skip ~ termIdentifier ~ arrow ~ expr ~ rpar).map {
      case None ~ x ~ _ ~ e ~ _ =>
        val body = Tree.replace(x, App(Var(x), UnitLiteral), e)
        Fix(None, Bind(Identifier(0, "_"), Bind(x, body)))
      case Some(_ ~ Var(n) ~ _ ~ tp ~ _) ~ x ~ _ ~ e ~ _ =>
        val body = Tree.replace(
          x,
          Inst(
            App(Var(x), UnitLiteral),
            Primitive(Minus, List(Var(n), NatLiteral(1)))
          ),
          e
        )
        Fix(Some(Bind(n, tp)), Bind(n, Bind(x, body)))
    }

  lazy val fold: Syntax[Tree] =
    (foldK.skip ~ asK.skip ~ typeExpr ~ rsbra.skip ~
    lpar.skip ~ expr ~ rpar.skip).map {
      case ty ~ e  => Fold(ty, e)
    }

  lazy val unfoldIn: Syntax[Tree] =
    (unfoldK.skip ~ valK.skip ~ termIdentifier ~ assignation.skip ~ expr ~ semicolon.skip ~
     expr).map {
      case x ~ e1 ~ e2 => Unfold(e1, Bind(x, e2))
    }

  lazy val unfoldPositiveIn: Syntax[Tree] =
    (unfoldPositiveK.skip ~ valK.skip ~ termIdentifier ~ assignation.skip ~ expr ~ semicolon.skip ~
     expr).map {
      case x ~ e1 ~ e2 => UnfoldPositive(e1, Bind(x, e2))
    }

  lazy val letIn: Syntax[Tree] =
     (valK.skip ~ termIdentifier ~ opt(lsbra.skip ~ typeExpr ~ rsbra.skip) ~ assignation.skip ~
      expr ~ semicolon.skip ~ expr).map {
      case x ~ optTy ~ e ~ e2 =>
        LetIn(optTy, e, Bind(x, e2))
    }

  lazy val parExpr: Syntax[Tree] = {
    (lpar ~ repsep(expr, comma.unit()) ~ rpar).map {
      case _ ~ l ~ _ =>
        if(l.isEmpty) UnitLiteral
        else if(l.size == 1) l.head
        else {
          val h = l.reverse.head
          val r = l.reverse.tail.reverse
          r.foldRight(h) { case (e, acc) => Pair(e, acc) }
        }
    }
  }

  sealed abstract class AppArgument
  case class TypeAppArg(ty: Tree) extends AppArgument
  case class TermAppArg(t: Tree) extends AppArgument
  case class ErasableAppArg(t: Tree) extends AppArgument

  lazy val sBracketAppArg: Syntax[AppArgument] = {
    (lsbra.skip ~ typeExpr ~ rsbra.skip).map { case e => TypeAppArg(e) }
  }

  lazy val bracketAppArg: Syntax[AppArgument] = {
    (dlbra.skip ~ expr ~ drbra.skip).map { case ty => ErasableAppArg(ty) }
  }

  lazy val parAppArg: Syntax[AppArgument] = {
    simpleExpr.map { case e => TermAppArg(e) }
  }

  lazy val appArg: Syntax[AppArgument] = parAppArg | bracketAppArg | sBracketAppArg

  def createApp(args: Seq[AppArgument], fun: Tree): Tree = {
    args.foldLeft(fun) {
      case (acc, TypeAppArg(ty))     => TypeApp(acc, ty)
      case (acc, TermAppArg(t))      => App(acc, t)
      case (acc, ErasableAppArg(t))  => Inst(acc, t)
    }
  }

  lazy val application: Syntax[Tree] = {
    (simpleExpr ~ many(appArg)).map { case f ~ args => createApp(args, f) }
  }

  lazy val macroTermArg: Syntax[(Boolean, Tree)] =
    simpleExpr.map((true, _))

  lazy val macroTypeArg: Syntax[(Boolean, Tree)] =
    (lsbra.skip ~ typeExpr ~ rsbra.skip).map((false, _))

  lazy val macroTypeInst: Syntax[Tree] = {
    (typeIdentifier ~ many(macroTermArg | macroTypeArg)).map {
      case id ~ Nil => Var(id)
      case id ~ args => MacroTypeInst(Var(id), args)
    }
  }

  lazy val eitherMatch: Syntax[Tree] =
    (matchK.skip ~ expr ~ lbracase.skip ~
                   leftK.skip ~ lpar.skip ~ termVariable ~ rpar.skip ~ arrow.skip ~ optBracketExpr ~
      caseK.skip ~ rightK.skip ~ lpar.skip ~ termVariable ~ rpar.skip ~ arrow.skip ~ optBracketExpr ~
    rbra.skip
    ).map {
      case (e ~ Var(v1) ~ e1 ~ Var(v2) ~ e2) =>
        EitherMatch(e, Bind(v1, e1), Bind(v2, e2))
    }

  val prefixedApplication: Syntax[Tree] = prefixes(not, application)({
      case _ => throw new java.lang.Exception("Not implemented")
    }, {
      case _ => throw new java.lang.Exception("Not implemented")
    })

  val operator: Syntax[Tree] = {
    operators(prefixedApplication)(
      mul | div | and is LeftAssociative,
      plus | minus | or is LeftAssociative,
      lt | gt | lteq | gteq is LeftAssociative,
      eq is LeftAssociative)({
      case (x, OperatorToken(op), y) => Primitive(op, List(x,y))
    }, {
      case Primitive(op, x ::  y ::  Nil) => (x, OperatorToken(op), y)
    })
  }

  lazy val condition: Syntax[Tree] = {
    (ifK.skip ~ lpar.skip ~ expr ~ rpar.skip ~ bracketExpr ~ elseK.skip ~ bracketExpr).map {
      case cond ~ vTrue ~ vFalse => IfThenElse(cond, vTrue, vFalse)
    }
  }

  lazy val optBracketExpr: Syntax[Tree] = expr | bracketExpr

  lazy val bracketExpr: Syntax[Tree] = {
    (lbra ~ expr ~ rbra).map { case _ ~ e ~ _ => e }
  }

  lazy val simpleExpr: Syntax[Tree] = literal | parExpr | fixpoint |
    function | keep |
    error | fold | lambdaAbs

  lazy val macroTypeDeclaration: Syntax[Tree] = {
    (lsbra.skip ~ typeK.skip ~ typeIdentifier ~
      many((lpar.skip ~ termIdentifier ~ rpar.skip) |
           (lsbra.skip ~ typeIdentifier ~ rsbra.skip)) ~
      assignation.skip ~ typeExpr ~ rsbra.skip ~ expr).map {
      case id ~ args ~ ty ~ rest =>
        MacroTypeDecl(args.foldRight(ty)((arg, acc) => Bind(arg, acc)), Bind(id, rest))
    }
  }

  lazy val expr: Syntax[Tree] = recursive {
    condition | eitherMatch | letIn | unfoldIn | unfoldPositiveIn |
    defFunction | operator | macroTypeDeclaration
  }

  val exprParser = LL1(expr)

  def apply(it: Iterator[Token]): LL1.ParseResult[Tree] = exprParser(it)
}
