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

case class DefinitionToken(value: String, range: (Int, Int)) extends Token

case class KeyWordToken(value: String, range: (Int, Int)) extends Token
case class SeparatorToken(value: String, range: (Int, Int)) extends Token
case class BooleanToken(value: Boolean, range: (Int, Int)) extends Token
case class NumberToken(value: BigInt, range: (Int, Int)) extends Token
case class StringToken(value: String, range: (Int, Int)) extends Token
case class NullToken(range: (Int, Int)) extends Token
case class SpaceToken(range: (Int, Int)) extends Token
case class UnknownToken(content: String, range: (Int, Int)) extends Token

case class IfToken(range: (Int, Int)) extends Token
case class ElseToken(range: (Int, Int)) extends Token

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
    oneOf("-+/*!<>")
      |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r)},

    word("&&")
      |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },
    word("||")
      |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },
    word("==")
      |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },
    word("!=")
      |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },
    word("<=")
        |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },
    word(">=")
    |> { (cs, r) => OperatorToken(stringToOperator(cs.mkString), r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => AssignationToken(r) },

    // Separator
    oneOf("{},().")
      |> { (cs, r) => SeparatorToken(cs.mkString, r) },
    word("=>")
      |> { (cs, r) => SeparatorToken(cs.mkString, r) },

    // Space
    many1(whiteSpace)
      |> { (_, r) => SpaceToken(r) },

    // Booleans
    word("true")
      |> { (_, r) => BooleanToken(true, r) },
    word("false")
      |> { (_, r) => BooleanToken(false, r) },

    // Definitions
    word("val") | word("def")
      |> { (cs, r) => DefinitionToken(cs.mkString, r) },

      // Keywords
    word("if") | word("else") | word("case") | word("in") | word("match") | word("fix") | word("fun") | word("Right") | word("Left")
      |> { (cs, r) => KeyWordToken(cs.mkString, r) },

    // Strings
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

    // Var
    elem(c => c.isLetter) ~
    many { elem(c => c.isLetterOrDigit || c == '_' || c == '$') }
      |> { (cs, r) => VarToken(cs.mkString, r) },

    // Numbers
    opt {
      elem('-')
    } ~
    {
      elem('0') |
      nonZero ~ many(digit)
    } ~
    opt {
      elem('.') ~ many1(digit)
    } ~
    opt {
      oneOf("eE") ~
      opt(oneOf("+-")) ~
      many1(digit)
    }
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

case object DefinitionClass extends TokenClass("<definition>")
case object VarClass extends TokenClass("<var>")
case class OperatorClass(op: Operator) extends TokenClass("<operator>")
case class SeparatorClass(value: String) extends TokenClass(value)
case object BooleanClass extends TokenClass("<boolean>")
case object NumberClass extends TokenClass("<number>")
case object StringClass extends TokenClass("<string>")
case object NullClass extends TokenClass("<null>")
case object NoClass extends TokenClass("<error>")
case object AssignationClass extends TokenClass("<assignation>")
case class KeyWordClass(value: String) extends TokenClass(value)

object ScalaParser extends Parsers[Token, TokenClass]
    with Graphs[TokenClass] with Grammars[TokenClass]
    with Operators {

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value, range) => SeparatorClass(value)
    case BooleanToken(value, range) => BooleanClass
    case NumberToken(value, range) => NumberClass
    case DefinitionToken(value, range) => DefinitionClass
    case VarToken(content, range) => VarClass
    case OperatorToken(op, range) => OperatorClass(op)
    case AssignationToken(range) => AssignationClass
    case KeyWordToken(value, range) => KeyWordClass(value)
    case _ => NoClass
  }

  val booleanValue = accept(BooleanClass) {
    case BooleanToken(value, range) => BoolLiteral(value)
  }
  val numberValue = accept(NumberClass) {
    case NumberToken(value, range) => NatLiteral(value)
  }

  implicit def separator(s: String) = accept(SeparatorClass(s)) {
    case SeparatorToken(_, range) => range
  }


  val definitionValue = accept(DefinitionClass) {
    case DefinitionToken(value, range) => BottomTree
  }

  val varValue = accept(VarClass) {
    case VarToken(content, range) => Var(None(), content)
  }

  val assignation = accept(AssignationClass) {
    case AssignationToken(range) => BottomTree
  }

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
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Div, List(x, y))
      f
  }

  val div = accept(OperatorClass(Div)) {
    case _ =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(Div, List(x, y))
      f
  }



  val openP = elem(SeparatorClass("("))
  val closeP = elem(SeparatorClass(")"))
  val openB = elem(SeparatorClass("{"))
  val closeB = elem(SeparatorClass("}"))
  val comma = elem(SeparatorClass(","))
  val dot = elem(SeparatorClass("."))
  val arr = elem(SeparatorClass("=>"))
  val in = elem(KeyWordClass("in"))
  val ift = elem(KeyWordClass("if"))
  val elset = elem(KeyWordClass("else"))
  val fix = elem(KeyWordClass("fix"))
  val fun = elem(KeyWordClass("fun"))
  val right = elem(KeyWordClass("Right"))
  val left = elem(KeyWordClass("Left"))
  val matchK = elem(KeyWordClass("match"))
  val caseK = elem(KeyWordClass("case"))

  lazy val basic: Parser[Tree] = numberValue | openP ~>~ expr ~<~ closeP | booleanValue | varValue | app

  lazy val operator: Parser[Tree] = recursive {
    operators(basic)(
      mul | div is LeftAssociative,
      plus | minus is LeftAssociative)
    }

  /*lazy val definition: Parser[Tree] = recursive {
      oneOf(let, operator | condition | tuple)
    }*/

  def makeResult(s: List[Tree]): Tree = s match {
    case Nil() => UnitLiteral
    case e::Nil() => e
    case e::t => e match {
      case LetIn(None(), expr, Bind(x, _)) =>
        LetIn(None(), expr, Bind(x, makeResult(t)))
      case LetIn(_, _, _) => UnitLiteral
      case e: Tree => e
    }
  }

  def scalaToStainlessList(l: scala.collection.immutable.List[Tree]): List[Tree] = {
    if(l.isEmpty) Nil()
    else Cons(l.head, scalaToStainlessList(l.tail))
  }

  lazy val let = recursive {
    (definitionValue ~ varValue ~ assignation ~ expr).map {
      case _ ~ x ~ _ ~ e => LetIn(None(), e, Bind(Some(x), x))
    }
  }

  lazy val fixpoint: Parser[Tree] = recursive {
    (fix ~ openP ~ varValue ~ arr ~ result ~ closeP).map {
      case _ ~ _ ~ v ~ _ ~ e ~ _ => Fix(Bind(Some(v), e))
    }
  }

  lazy val matchE: Parser[Tree] = recursive {
    (matchK ~ expr ~ openB ~
    caseK ~ left ~ openP ~ varValue ~ closeP ~ arr ~ expr ~
    caseK ~ right ~ openP ~ varValue ~ closeP ~ arr ~ expr ~
    closeB).map {
      case (_ ~ e ~ _ ~ _ ~ _ ~ _ ~ v1 ~ _ ~ _ ~ e1 ~
      _ ~ _ ~ _ ~ v2 ~ _ ~ _ ~ e2 ~ _) =>
      EitherMatch(e, Bind(Some(v1), e1), Bind(Some(v2), e2))
    }
  }

  lazy val function: Parser[Tree] = recursive {
    (fun ~ varValue ~ arr ~ openB ~ result ~ closeB).map {
      case _ ~ v ~ _ ~  _ ~ e ~ _ => Lambda(None(), Bind(Some(v), e))
    }
  }

  lazy val leftT: Parser[Tree] = recursive {
    (left ~ openP ~ expr ~ closeP).map {
      case _ ~ _ ~ e ~ _ => LeftTree(e)
    }
  }

  lazy val rightT: Parser[Tree] = recursive {
    (right ~ openP ~ expr ~ closeP).map {
      case  _ ~ _ ~ e ~ _ => RightTree(e)
    }
  }

  lazy val result =
    (repsep(expr, in)).map {
      case s =>
        println(s.size)
        makeResult(scalaToStainlessList(s.toList))
    }

  lazy val expr: Parser[Tree] = recursive {
    oneOf(operator | app | condition | let | tuple | function | fixpoint | leftT | rightT | matchE | openP)
  }

  lazy val condition: Parser[Tree] = recursive {
    (ift ~ openP ~ expr ~ closeP ~ openB ~ expr ~ closeB ~ elset ~ openB ~ expr ~ closeB).map {
      case _ ~ _ ~ cond ~ _ ~ _ ~ vTrue ~ _ ~ _ ~ _ ~ vFalse ~ _ => IfThenElse(cond, vTrue, vFalse)
    }
  }

  val app: Parser[Tree] = recursive {
    (openB ~ expr ~ openP ~ repsep(expr, comma) ~ closeP ~ closeB).map {
      case _ ~ f ~ _ ~ args ~ _ ~ _  => makeApp(f, scalaToStainlessList(args.toList.reverse))
    }
  }

  def makeApp(f: Tree, args: List[Tree]): Tree = args match {
    case Nil() => App(f, UnitLiteral)
    case x::Nil() => App(f, x)
    case x::t => App(makeApp(f, t), x)
  }

  lazy val tuple = recursive {
    (openP ~ expr ~ comma ~ rep1sep(expr, comma) ~ closeP).map {
      case _ ~ e1 ~ _ ~ vs ~ _ => Pair(e1, makeTuple(scalaToStainlessList(vs.toList)))
    }
  }

  def apply(it: Iterator[Token]): ParseResult[Tree] = result(it)

  def makeTuple(s: List[Tree]): Tree = s match {
    case Nil() => BottomTree
    case x::Nil() => x
    case x::t => Pair(x, makeTuple(t))
  }

}