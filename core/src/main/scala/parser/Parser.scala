package core
package parser

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

import core.trees._
import core.Bench.bench

import Util._

sealed abstract class Token {
  val range: (Int, Int)
}

case class AssignationToken(range: (Int, Int)) extends Token

case class KeyWordToken(value: String, range: (Int, Int)) extends Token
case class SeparatorToken(value: String, range: (Int, Int)) extends Token
case class BooleanToken(value: Boolean, range: (Int, Int)) extends Token
case class NumberToken(value: BigInt, range: (Int, Int)) extends Token
case class StringToken(value: String, range: (Int, Int)) extends Token
case class NullToken(range: (Int, Int)) extends Token
case class SpaceToken(range: (Int, Int)) extends Token
case class UnknownToken(content: String, range: (Int, Int)) extends Token

case class UnitToken(range: (Int, Int)) extends Token

case class VarToken(content: String, range: (Int, Int)) extends Token

case class OperatorToken(op: Operator, range: (Int, Int)) extends Token
case class TypeToken(content: String, range: (Int, Int)) extends Token

/*sealed abstract class Value {
  val range: (Int, Int)
}

case class BooleanValue(value: Boolean, range: (Int, Int)) extends Value
case class NumberValue(value: BigInt, range: (Int, Int)) extends Value
case class StringValue(value: String, range: (Int, Int)) extends Value
case class NullValue(range: (Int, Int)) extends Value
*/
object ScalaLexer extends Lexers[Token, Char, Int] with CharRegExps {

  val lexer = Lexer(
    // Operators
    oneOf("-+/*!<>") | word("&&") |  word("||") |
    word("==") | word("!=") | word("<=") | word(">=")
    |> { (cs, r) => OperatorToken(Operator.fromString(cs.mkString).get, r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => AssignationToken(r) },

    // Separator
    oneOf("{},|().:[]") | word("=>")
      |> { (cs, r) => SeparatorToken(cs.mkString, r) },

    // Space
    many1(whiteSpace)
      |> { (_, r) => SpaceToken(r) },

    // Booleans
    word("true")
      |> { (_, r) => BooleanToken(true, r) },
    word("false")
      |> { (_, r) => BooleanToken(false, r) },

      // Keywords
    (elem('{') ~ many { elem(c => c == '\n' || c == ' ') } ~ word("case")) |
    word("if") | word("else") | word("case") | word("in") | word("match") |
    word("with") | word("end") |
    word("fix") | word("fun") | word("Right") | word("Left") | word("val") |
    word("def") | word("Error") | word("First") | word("Second") | word("Fold") |
    word("Unfold") | word("UnfoldPositive") | word("Decreases") | word("Pi") | word("Sigma") | word("Forall") | word("Lambda") |
    word("type")
      |> { (cs, r) => KeyWordToken(cs.mkString.replaceAll("""[ \n]""", ""), r) },

    word("Bool") | word("Unit") | word("Nat") | word("Rec") | word("Top")
      |>  { (cs, r) => TypeToken(cs.mkString, r) },

    // Var
    elem(c => c.isLetter) ~
    many { elem(c => c.isLetterOrDigit || c == '_' || c == '$') }
      |> { (cs, r) => VarToken(cs.mkString, r) },

    elem('"') ~
    many {
      elem(c => c != '"' && c != '\\' && !c.isControl) |
      elem('\\') ~ (oneOf("\"\\/bfnrt") | elem('u') ~ hex.times(4))
    } ~
    elem('"')
      |> { (cs, r) => {
        val string = cs.mkString
        StringToken(string.slice(1, string.length - 1), r)
}},

    // Numbers
    elem('0') | (nonZero ~ many(digit))
      |> { (cs, r) => NumberToken(cs.mkString.toInt, r) },

    elem('/') ~ elem('/') ~ many { elem(c => c != '\n' )}
      |> { (_, r) => SpaceToken(r) },

  ) onError {
    (cs, r) => UnknownToken(cs.mkString, r)
  }

  def apply(it: Iterator[Char]): Iterator[Token] = {
    val source = Source.fromIterator(it, IndexPositioner)
    val tokens = lexer.spawn(source)
    tokens.filter(!_.isInstanceOf[SpaceToken])
  }
}

sealed abstract class TokenClass(repr: String) {
  override def toString = repr
}

case object VarClass extends TokenClass("<var>")
case class OperatorClass(op: Operator) extends TokenClass(s"<operator>")
case class SeparatorClass(value: String) extends TokenClass(value)
case object BooleanClass extends TokenClass("<boolean>")
case object NumberClass extends TokenClass("<number>")
case object StringClass extends TokenClass("<string>")
case object NoClass extends TokenClass("<error>")
case object UnitClass extends TokenClass("<unit>")
case object AssignationClass extends TokenClass("<assignation>")
case class KeyWordClass(value: String) extends TokenClass(value)
case class TypeClass(value: String) extends TokenClass("<type>")

object ScalaParser extends Syntaxes[Token, TokenClass] with Operators {

  import Implicits._

  var id = 0

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value, range) => SeparatorClass(value)
    case BooleanToken(value, range) => BooleanClass
    case NumberToken(value, range) => NumberClass
    case VarToken(content, range) => VarClass
    case OperatorToken(op, range) => OperatorClass(op)
    case AssignationToken(range) => AssignationClass
    case KeyWordToken(value, range) => KeyWordClass(value)
    case UnitToken(range) => UnitClass
    case TypeToken(content, range) => TypeClass(content)
    case StringToken(content, range) => StringClass
    case _ => NoClass
  }

  def newId: Int = {
    id = id + 1
    id
  }

  val assignation: Syntax[Token] = elem(AssignationClass)
  val lpar: Syntax[Token] = elem(SeparatorClass("("))
  val rpar: Syntax[Token] = elem(SeparatorClass(")"))
  val lbra: Syntax[Token] = elem(SeparatorClass("{"))
  val rbra: Syntax[Token] = elem(SeparatorClass("}"))
  val lsbra: Syntax[Token] = elem(SeparatorClass("["))
  val rsbra: Syntax[Token] = elem(SeparatorClass("]"))
  val comma: Syntax[Token] = elem(SeparatorClass(","))
  val pipe: Syntax[Token] = elem(SeparatorClass("|"))
  val colon: Syntax[Token] = elem(SeparatorClass(":"))
  val appK: Syntax[Token] = elem(SeparatorClass("\\"))
  val tupleK: Syntax[Token] = elem(SeparatorClass("\\("))
  val dot: Syntax[Token] = elem(SeparatorClass("."))
  val arrow: Syntax[Token] = elem(SeparatorClass("=>"))
  val inK: Syntax[Token] = elem(KeyWordClass("in"))
  val ifK: Syntax[Token] = elem(KeyWordClass("if"))
  val elseK: Syntax[Token] = elem(KeyWordClass("else"))
  val fixK: Syntax[Token] = elem(KeyWordClass("fix"))
  val funK: Syntax[Token] = elem(KeyWordClass("fun"))
  val rightK: Syntax[Token] = elem(KeyWordClass("Right"))
  val leftK: Syntax[Token] = elem(KeyWordClass("Left"))
  val firstK: Syntax[Token] = elem(KeyWordClass("First"))
  val secondK: Syntax[Token] = elem(KeyWordClass("Second"))
  val matchK: Syntax[Token] = elem(KeyWordClass("match"))
  val caseK: Syntax[Token] = elem(KeyWordClass("case"))
  val lbracase: Syntax[Token] = elem(KeyWordClass("{case"))
  val valK: Syntax[Token] = elem(KeyWordClass("val"))
  val defK: Syntax[Token] = elem(KeyWordClass("def"))
  val recK: Syntax[Token] = elem(TypeClass("Rec"))
  val errorK: Syntax[Token] = elem(KeyWordClass("Error"))
  val foldK: Syntax[Token] = elem(KeyWordClass("Fold"))
  val unfoldK: Syntax[Token] = elem(KeyWordClass("Unfold"))
  val unfoldPositiveK: Syntax[Token] = elem(KeyWordClass("UnfoldPositive"))
  val decreasesK: Syntax[Token] = elem(KeyWordClass("Decreases"))
  val piK: Syntax[Token] = elem(KeyWordClass("Pi"))
  val sigmaK: Syntax[Token] = elem(KeyWordClass("Sigma"))
  val forallK: Syntax[Token] = elem(KeyWordClass("Forall"))
  val lambdaK: Syntax[Token] = elem(KeyWordClass("Lambda"))
  val typeK: Syntax[Token] = elem(KeyWordClass("type"))

  val natType: Syntax[Tree] = accept(TypeClass("Nat")) { case _ => NatType }
  val boolType: Syntax[Tree] = accept(TypeClass("Bool")) { case _ => BoolType }
  val unitType: Syntax[Tree] = accept(TypeClass("Unit")) { case _ => UnitType }
  val topType: Syntax[Tree] = accept(TypeClass("Top")) { case _ => TopType }

  val literalType: Syntax[Tree] = natType | boolType | unitType | topType

  lazy val parTypeExpr: Syntax[Tree] = {
    (lpar ~ rep1sep(typeExpr, comma.unit()) ~ rpar).map {
      case _ ~ l ~ _ =>
        if(l.size == 1) l.head
        else {
          val h = l.reverse.head
          val r = l.reverse.tail.reverse
          r.foldRight(h) { case (e, acc) => SigmaType(e, Bind(Identifier(newId, "_S"), acc)) }
        }
    }
  }

  lazy val piType: Syntax[String] = accept(SeparatorClass("=>"))({
      case SeparatorToken("=>", _) => "=>"
    }, {
      case "=>" => Seq(SeparatorToken("=>", (0,0)))
      case _ => Seq()
    })

  lazy val bPiType: Syntax[Tree] = {
    (piK ~ lpar ~ variable ~ colon ~ typeExpr ~ comma ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ Var(id) ~ _ ~ ty1 ~ _ ~ ty2 ~ _ => PiType(ty1, Bind(id, ty2))
    }
  }

  lazy val bSigmaType: Syntax[Tree] = {
    (sigmaK ~ lpar ~ variable ~ colon ~ typeExpr ~ comma ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ Var(id) ~ _ ~ ty1 ~ _ ~ ty2 ~ _ => SigmaType(ty1, Bind(id, ty2))
    }
  }

  lazy val bForallType: Syntax[Tree] = {
    (forallK ~ lpar ~ variable ~ opt(colon ~ typeExpr) ~ comma ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ Var(id) ~ Some(_ ~ ty1)~  _ ~ ty2 ~ _ => IntersectionType(ty1, Bind(id, ty2))
      case _ ~ _ ~ Var(id) ~ None ~ _ ~ ty2 ~ _ => PolyForallType(Bind(id, ty2))
    }
  }


  lazy val recType: Syntax[Tree] = {
    (recK ~ lpar ~ expression ~ rpar ~ lpar ~ variable ~ arrow ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ n ~ _ ~ _ ~ Var(alpha) ~  _ ~ t ~ _ => RecType(n, Bind(alpha, t))
    }
  }

  lazy val refinementType: Syntax[Tree] = {
    (lbra ~ variable ~ colon ~ typeExpr ~ pipe ~ expression ~ rbra).map {
      case _ ~ Var(x) ~ _ ~ ty ~ _ ~ p ~ _ => RefinementType(ty, Bind(x, p))
    }
  }

  lazy val operatorType: Syntax[Tree] = {
    operators(simpleTypeExpr)(
      plus is LeftAssociative,
      piType is RightAssociative,
      eq is LeftAssociative
    )({
      case (ty1, "=>", ty2) => PiType(ty1, Bind(Identifier(newId, "_X"), ty2))
      case (ty1, "+", ty2) => SumType(ty1, ty2)
      case (ty1, "==", ty2) => EqualityType(ty1, ty2)
    }, {
      case PiType(ty1, Bind(_, ty2)) => (ty1, "=>", ty2)
      case SumType(ty1, ty2) => (ty1, "+", ty2)
      case EqualityType(ty1, ty2) => (ty1, "==", ty2)
    })
  }

  lazy val simpleTypeExpr: Syntax[Tree] = literalType | parTypeExpr | recType | refinementType | variable | bPiType | bSigmaType | bForallType

  lazy val typeExpr: Syntax[Tree] = recursive {
    operatorType
  }

  val boolean: Syntax[Tree] = accept(BooleanClass) { case BooleanToken(value, _) => BooleanLiteral(value) }
  val number: Syntax[Tree] = accept(NumberClass) { case NumberToken(value, _) => NatLiteral(value) }
  val variable: Syntax[Tree] = accept(VarClass) { case VarToken(content, _) => Var(Identifier(0, content)) }
  val unit: Syntax[Tree] = accept(UnitClass) { case _ => UnitLiteral }

  val literal: Syntax[Tree] = variable | number | boolean | unit

  def opParser(op: Operator): Syntax[String] = {
    accept(OperatorClass(op))({
      case OperatorToken(op, _) => op.toString
    }, {
      case s if (op.toString == s) => Seq(OperatorToken(op, (0,0)))
      case _ => Seq()
    })
  }

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
    (lambdaK ~ variable ~ arrow ~ bracketExpr).map {
      case _ ~ Var(x) ~ _ ~ e => Abs(Bind(x, e))
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

  lazy val sBracketArg: Syntax[DefArgument] = {
    (lsbra ~ variable ~ rsbra).map { case _ ~ Var(v) ~ _ => TypeArgument(v) }
  }

  lazy val bracketArg: Syntax[DefArgument] = {
    (lbra ~ variable ~ colon ~ typeExpr ~ rbra).map {
      case _ ~ Var(v) ~ _ ~ ty ~ _ => ForallArgument(v, ty)
    }
  }

  lazy val parArg: Syntax[DefArgument] = {
    (lpar ~ variable ~ colon ~ typeExpr ~ rpar).map {
      case _ ~ Var(v) ~ _ ~ ty ~ _ => PiArgument(v, ty)
    }
  }

  lazy val argument: Syntax[DefArgument] = sBracketArg | bracketArg | parArg

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
    (defK ~ variable ~ many1(argument) ~ opt(retTypeP) ~ assignation ~ lbra ~ opt(measureP) ~
    expression ~ rbra ~ opt(expression)).map {
      case _ ~ Var(f) ~ args ~ retType ~ _ ~ _ ~ measure ~ e1 ~ _ ~ e2 =>
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

  lazy val retTypeP: Syntax[Tree] = { (colon ~ typeExpr).map { case _ ~ t => t } }
  lazy val measureP: Syntax[Tree] = { (decreasesK ~ lpar ~ expression ~rpar).map { case _ ~ _ ~ e ~ _ => e } }


  lazy val function: Syntax[Tree] = {
    (funK ~ many(argument) ~ arrow ~ bracketExpr).map {
      case _ ~ args ~ _ ~ e => createFun(args, None, e, Identifier(0, "__"))._1
    }
  }

  lazy val string: Syntax[String] = accept(StringClass) { case StringToken(content, _) => content }

  lazy val error: Syntax[Tree] = {
    (errorK ~ opt(lsbra ~ typeExpr ~ rsbra) ~ lpar ~ string ~ rpar).map {
      case _ ~ tpe ~ _ ~ s ~ _ => tpe match {
        case None => Error(s, None)
        case Some(_ ~ tp ~ _) => Error(s, Some(tp))
      }
    }
  }

  lazy val fixpoint: Syntax[Tree] =
    (fixK ~ opt(lsbra ~ variable ~ arrow ~ typeExpr ~ rsbra) ~
    lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ None ~ _ ~ Var(x) ~ _ ~ e ~ _ =>
        val body = Tree.replace(x, App(Var(x), UnitLiteral), e)
        Fix(None, Bind(Identifier(0, "_"), Bind(x, body)))
      case _ ~ Some(_ ~ Var(n) ~ _ ~ tp ~ _) ~ _ ~ Var(x) ~ _ ~ e ~ _ =>
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
    (foldK ~ opt(lsbra ~ typeExpr ~ rsbra) ~
    lpar ~ expression ~ rpar).map {
      case _ ~ None ~ _ ~ e ~ _  =>
        Fold(None, e)
      case _ ~ Some(_ ~ tp ~ _) ~ _ ~ e ~ _ =>
        Fold(Some(tp), e)
    }

  lazy val unfold: Syntax[Tree] =
    (unfoldK ~ lpar ~ expression ~ rpar ~ inK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ ~ _ ~ _ ~ Var(x) ~ _ ~ f ~ _ => Unfold(e, Bind(x, f))
    }

  lazy val unfoldPositive: Syntax[Tree] =
    (unfoldPositiveK ~ lpar ~ expression ~ rpar ~ inK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ ~ _ ~ _ ~ Var(x) ~ _ ~ f ~ _ => UnfoldPositive(e, Bind(x, f))
    }

  lazy val letIn: Syntax[Tree] =
    (valK ~ variable ~ opt(colon ~ typeExpr) ~ assignation ~ expression ~ inK ~ expression).map {
      case _ ~ Var(x) ~ None ~ _ ~ e ~ _ ~ e2 =>
        LetIn(None, e, Bind(x, e2))
      case _ ~ Var(x) ~ Some(_ ~ tp) ~ _ ~ e ~ _ ~ e2 =>
        LetIn(Some(tp), e, Bind(x, e2))
    }

  lazy val parExpr: Syntax[Tree] = {
    (lpar ~ repsep(expression, comma.unit()) ~ rpar).map {
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
    (lsbra ~ typeExpr ~ rsbra).map { case _ ~ e ~ _ => TypeAppArg(e) }
  }

  lazy val bracketAppArg: Syntax[AppArgument] = {
    (lbra ~ expression ~ rbra).map { case _ ~ ty ~ _ => ErasableAppArg(ty) }
  }

  lazy val parAppArg: Syntax[AppArgument] = {
    simpleExpr.map { case e => TermAppArg(e) }
  }

  lazy val appArg: Syntax[AppArgument] = parAppArg | bracketAppArg | sBracketAppArg

  def createApp(args: Seq[AppArgument], fun: Tree): Tree = {
    bench.time("createApp") {
      args.foldLeft(fun) {
        case (acc, TypeAppArg(ty))     => TypeApp(acc, ty)
        case (acc, TermAppArg(t))      => App(acc, t)
        case (acc, ErasableAppArg(t))  => Inst(acc, t)
      }
    }
  }

  lazy val application: Syntax[Tree] = {
    (simpleExpr ~ many(appArg)).map { case f ~ args => createApp(args, f) }
  }

  lazy val eitherMatch: Syntax[Tree] =
    (matchK ~ expression ~ lbracase ~
            leftK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    caseK ~ rightK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    rbra).map {
      case (_ ~ e ~ _ ~ _ ~ _ ~ Var(v1) ~ _ ~ _ ~ e1 ~
      _ ~ _ ~ _ ~ Var(v2) ~ _ ~ _ ~ e2 ~ _) =>
      EitherMatch(e, Bind(v1, e1), Bind(v2, e2))
    }

  lazy val left: Syntax[Tree] =
    (leftK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => LeftTree(e)
    }

  lazy val right: Syntax[Tree] =
    (rightK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => RightTree(e)
    }

  lazy val first: Syntax[Tree] =
    (firstK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => First(e)
    }

  lazy val second: Syntax[Tree] =
    (secondK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => Second(e)
    }

  val prefixedApplication: Syntax[Tree] = prefixes(not, application)({
      case _ => throw new java.lang.Exception("55")
    }, {
      case _ => throw new java.lang.Exception("6")
    })

  val operator: Syntax[Tree] = {
    operators(prefixedApplication)(
      mul | div | and is LeftAssociative,
      plus | minus | or is LeftAssociative,
      lt | gt | lteq | gteq is LeftAssociative,
      eq is LeftAssociative)({
      case (x, op, y) => Primitive(Operator.fromString(op).get, List(x,y))
    }, {
      case Primitive(op, x ::  y ::  Nil) => (x, op.toString, y)
    })
  }

  lazy val condition: Syntax[Tree] = {
    (ifK ~ lpar ~ expression ~ rpar ~ optBracketExpr ~ elseK ~ optBracketExpr).map {
      case _ ~ _ ~ cond ~ _ ~ vTrue ~ _ ~ vFalse => IfThenElse(cond, vTrue, vFalse)
    }
  }

  lazy val optBracketExpr: Syntax[Tree] = expression | bracketExpr

  lazy val bracketExpr: Syntax[Tree] = {
    (lbra ~ expression ~ rbra).map { case _ ~ e ~ _ => e }
  }

  lazy val simpleExpr: Syntax[Tree] = literal | parExpr | fixpoint | function | left | right | first | second |
    error | fold | unfold | unfoldPositive | lambdaAbs

  lazy val expression: Syntax[Tree] = recursive {
    condition | eitherMatch | letIn | defFunction | operator
  }

  def apply(it: Iterator[Token]): ParseResult[Tree] = expression(it)
}
