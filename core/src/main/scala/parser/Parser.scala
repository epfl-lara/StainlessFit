package parser

import scallion.input._
import scallion.lexing._
import scallion.parsing._

import _root_.trees._
import scallion.parsing.visualization.Graphs
import scallion.parsing.visualization.Grammars

import stainless.annotation._
import stainless.collection._
import stainless.lang._

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


/*sealed abstract class Value {
  val range: (Int, Int)
}

case class BooleanValue(value: Boolean, range: (Int, Int)) extends Value
case class NumberValue(value: BigInt, range: (Int, Int)) extends Value
case class StringValue(value: String, range: (Int, Int)) extends Value
case class NullValue(range: (Int, Int)) extends Value
*/
object ScalaLexer extends Lexers[Token, Char, Int] with CharRegExps {

  private def stringToOperator(str: String): Operator = str match {
    case "!" => Not
    case "&&" => And
    case "||" => Or
    case "+" => Plus
    case "-" => Minus
    case "*" => Mul
    case "/" => Div
    case "==" => Eq
    case "!=" => Neq
    case "<=" => Lteq
    case ">=" => Gteq
    case "<" => Lt
    case ">" => Gt
    case _ => Nop
  }

  val lexer = Lexer(
    // Operators
    oneOf("-+/*!<>") | word("&&") |  word("||") |
    word("==") | word("!=") |word("<=") | word(">=")
    |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => AssignationToken(r) },

    word("")
      |> { (cs, r) => UnitToken(r) },


    // Separator
    oneOf("{},().\\:") | word("=>")
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
    word("if") | word("else") | word("case") | word("in") | word("match") |
    word("fix") | word("fun") | word("Right") | word("Left") | word("val")
      |> { (cs, r) => KeyWordToken(cs.mkString, r) },

    // Var
    elem(c => c.isLetter) ~
    many { elem(c => c.isLetterOrDigit || c == '_' || c == '$') }
      |> { (cs, r) => VarToken(cs.mkString, r) },

    // Numbers
    elem('0') | (nonZero ~ many(digit))
      |> { (cs, r) => NumberToken(cs.mkString.toInt, r) }

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

object ScalaParser extends Parsers[Token, TokenClass]
    with Graphs[TokenClass] with Grammars[TokenClass]
    with Operators {

  def scalaToStainlessList(l: scala.collection.immutable.List[Tree]): List[Tree] = {
    if(l.isEmpty) Nil()
    else Cons(l.head, scalaToStainlessList(l.tail))
  }

  def makeApp(f: Tree, args: List[Tree]): Tree = args match {
    case Nil() => App(f, UnitLiteral)
    case x::Nil() => App(f, x)
    case x::t => App(makeApp(f, t), x)
  }

  def makeTuple(s: List[Tree]): Tree = s match {
    case Nil() => BottomTree
    case x::Nil() => x
    case x::t => Pair(x, makeTuple(t))
  }

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value, range) => SeparatorClass(value)
    case BooleanToken(value, range) => BooleanClass
    case NumberToken(value, range) => NumberClass
    case VarToken(content, range) => VarClass
    case OperatorToken(op, range) => OperatorClass(op)
    case AssignationToken(range) => AssignationClass
    case KeyWordToken(value, range) => KeyWordClass(value)
    case UnitToken(range) => UnitClass
    case _ => NoClass
  }

  val assignation = elem(AssignationClass)
  val lpar = elem(SeparatorClass("("))
  val rpar = elem(SeparatorClass(")"))
  val lbra = elem(SeparatorClass("{"))
  val rbra = elem(SeparatorClass("}"))
  val comma = elem(SeparatorClass(","))
  val colon = elem(SeparatorClass(":"))
  val appK = elem(SeparatorClass("\\"))
  val dot = elem(SeparatorClass("."))
  val arrow = elem(SeparatorClass("=>"))
  val inK = elem(KeyWordClass("in"))
  val ifK = elem(KeyWordClass("if"))
  val elseK = elem(KeyWordClass("else"))
  val fixK = elem(KeyWordClass("fix"))
  val funK = elem(KeyWordClass("fun"))
  val rightK = elem(KeyWordClass("Right"))
  val leftK = elem(KeyWordClass("Left"))
  val matchK = elem(KeyWordClass("match"))
  val caseK = elem(KeyWordClass("case"))
  val valK = elem(KeyWordClass("val"))


  val boolean = accept(BooleanClass) { case BooleanToken(value, _) => BoolLiteral(value) }

  val number = accept(NumberClass) { case NumberToken(value, _) => NatLiteral(value) }

  val variable = accept(VarClass) { case VarToken(content, _) => Var(None(), content) }

  val unit = accept(UnitClass) { case _ => UnitLiteral }

  val literal = variable | number | boolean | unit

  val plus = accept(OperatorClass(Plus)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Plus, List(x, y))
      f
  }

  val minus = accept(OperatorClass(Minus)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Minus, List(x, y))
      f
  }

  val mul = accept(OperatorClass(Mul)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Mul, List(x, y))
      f
  }

  val div = accept(OperatorClass(Div)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Div, List(x, y))
      f
  }

  val and = accept(OperatorClass(And)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(And, List(x, y))
      f
  }

  val or = accept(OperatorClass(Or)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Or, List(x, y))
      f
  }

  val eq = accept(OperatorClass(Eq)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Eq, List(x, y))
      f
  }

  val not = accept(OperatorClass(Not)) {
    case _ => val f: Tree => Tree = (x: Tree) => Primitive(Not, List(x))
    f
  }

  lazy val basic: Parser[Tree] = literal | lpar ~>~ expression ~<~ rpar

  lazy val operator: Parser[Tree] = recursive {
    operators(prefixes(not, basic))(
      mul | div | and is LeftAssociative,
      plus | minus | or is LeftAssociative,
      eq is LeftAssociative)
    }

  lazy val typeExpression = expression

  lazy val function: Parser[Tree] = recursive {
    (funK ~ variable ~ colon ~ typeExpression ~ arrow ~ lbra ~ expression ~ rbra).map {
      case _ ~ x ~ _ ~ _ ~ _ ~ _ ~ e ~ _ => Lambda(None(), Bind(Some(x), e))
    }
  }

  lazy val fixpoint: Parser[Tree] = recursive {
    (fixK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ x ~ _ ~ e ~ _ => Fix(None(), Bind(None(), Bind(Some(x), e)))
    }
  }

  lazy val letIn: Parser[Tree] = recursive {
    (valK ~ variable ~ assignation ~ expression ~ expression).map {
      case _ ~ x ~ _ ~ e ~ e2 => LetIn(None(), e, Bind(Some(x), e2))
    }
  }

  lazy val application: Parser[Tree] = recursive {
    (appK ~ expression ~ lpar ~ repsep(expression, comma) ~ rpar).map {
      case _ ~ f ~ _ ~ args ~ _  => makeApp(f, scalaToStainlessList(args.toList.reverse))
    }
  }

  lazy val eitherMatch: Parser[Tree] = recursive {
    (matchK ~ expression ~ lbra ~
    caseK ~ leftK ~ lpar ~ variable ~ rpar ~ arrow ~ expression ~
    caseK ~ rightK ~ lpar ~ variable ~ rpar ~ arrow ~ expression ~
    rbra).map {
      case (_ ~ e ~ _ ~ _ ~ _ ~ _ ~ v1 ~ _ ~ _ ~ e1 ~
      _ ~ _ ~ _ ~ v2 ~ _ ~ _ ~ e2 ~ _) =>
      EitherMatch(e, Bind(Some(v1), e1), Bind(Some(v2), e2))
    }
  }

  lazy val left: Parser[Tree] = recursive {
    (leftK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => LeftTree(e)
    }
  }

  lazy val right: Parser[Tree] = recursive {
    (rightK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => RightTree(e)
    }
  }


  lazy val expression: Parser[Tree] = recursive {
    oneOf(application | operator | function | fixpoint | letIn | eitherMatch | left | right | unit
    )
  }

  lazy val condition: Parser[Tree] = recursive {
    (ifK ~ lpar ~ expression ~ rpar ~ lbra ~ expression ~ rbra ~ elseK ~ lbra ~ expression ~ rbra).map {
      case _ ~ _ ~ cond ~ _ ~ _ ~ vTrue ~ _ ~ _ ~ _ ~ vFalse ~ _ => IfThenElse(cond, vTrue, vFalse)
    }
  }

  lazy val tuple = recursive {
    (lpar ~ expression ~ comma ~ rep1sep(expression, comma) ~ rpar).map {
      case _ ~ e1 ~ _ ~ vs ~ _ => Pair(e1, makeTuple(scalaToStainlessList(vs.toList)))
    }
  }

  def apply(it: Iterator[Token]): ParseResult[Tree] = expression(it)
}