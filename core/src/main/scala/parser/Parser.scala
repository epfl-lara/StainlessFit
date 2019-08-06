package parser

import scallion.input._
import scallion.lexing._
import scallion.parsing._

import trees._

import scallion.parsing.visualization.Graphs
import scallion.parsing.visualization.Grammars

import stainless.annotation._
import stainless.collection._

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

    /*word("")
      |> { (cs, r) => UnitToken(r) },*/


    // Separator
    oneOf("{},().:[]") | word("=>")
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
    word("fix") | word("fun") | word("Right") | word("Left") | word("val") |
    word("def") | word("Error") | word("First") | word("Second") | word("fixdef") | word("Inst") | word("Fold") |
    word("Unfold")
      |> { (cs, r) => KeyWordToken(cs.mkString, r) },

    word("Bool") | word("Unit") | word("Nat") | word("Rec")
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

object ScalaParser extends Parsers[Token, TokenClass]
    with Graphs[TokenClass] with Grammars[TokenClass]
    with Operators {

  val stainlessNone = stainless.lang.None
  val stainlessSome = stainless.lang.Some
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

  val assignation = elem(AssignationClass)
  val lpar = elem(SeparatorClass("("))
  val rpar = elem(SeparatorClass(")"))
  val lbra = elem(SeparatorClass("{"))
  val rbra = elem(SeparatorClass("}"))
  val lsbra = elem(SeparatorClass("["))
  val rsbra = elem(SeparatorClass("]"))
  val comma = elem(SeparatorClass(","))
  val colon = elem(SeparatorClass(":"))
  val appK = elem(SeparatorClass("\\"))
  val tupleK = elem(SeparatorClass("\\("))
  val dot = elem(SeparatorClass("."))
  val arrow = elem(SeparatorClass("=>"))
  val inK = elem(KeyWordClass("in"))
  val ifK = elem(KeyWordClass("if"))
  val elseK = elem(KeyWordClass("else"))
  val fixK = elem(KeyWordClass("fix"))
  val funK = elem(KeyWordClass("fun"))
  val rightK = elem(KeyWordClass("Right"))
  val leftK = elem(KeyWordClass("Left"))
  val firstK = elem(KeyWordClass("First"))
  val secondK = elem(KeyWordClass("Second"))
  val matchK = elem(KeyWordClass("match"))
  val caseK = elem(KeyWordClass("case"))
  val valK = elem(KeyWordClass("val"))
  val defK = elem(KeyWordClass("def"))
  val recK = elem(TypeClass("Rec"))
  val errorK = elem(KeyWordClass("Error"))
  val instK = elem(KeyWordClass("Inst"))
  val fixdefK = elem(KeyWordClass("fixdef"))
  val foldK = elem(KeyWordClass("Fold"))
  val unfoldK = elem(KeyWordClass("Unfold"))

  val natType = accept(TypeClass("Nat")) { case _ => NatType }
  val boolType = accept(TypeClass("Bool")) { case _ => BoolType }
  val unitType = accept(TypeClass("Unit")) { case _ => UnitType }

  val literalType = natType | boolType | unitType

  lazy val basicType = literalType | parTypeExpr

  lazy val parTypeExpr: Parser[Tree] = {
    (lpar ~ rep1sep(typeExpr, comma) ~ rpar).map {
      case _ ~ l ~ _ =>
        if(l.size == 1) l.head
        else {
          val h = l.reverse.head
          val r = l.reverse.tail.reverse
          r.foldRight(h) { case (e, acc) => SigmaType(e, Bind(Identifier(newId, "_S"), acc)) }
        }
    }
  }

  lazy val sumType = accept(OperatorClass(Plus)) {
    case s =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => SumType(x, y)
      f
  }

  lazy val piType = accept(SeparatorClass("=>")) {
    case s =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => PiType(x, Bind(Identifier(newId, "_X"), y))
      f
  }

  lazy val recType: Parser[Tree] = {
    (recK ~ lpar ~ expression ~ rpar ~ lpar ~ variable ~ arrow ~ typeExpr ~ rpar).map {
      case _ ~ _ ~ n ~ _ ~ _ ~ Var(alpha) ~  _ ~ t ~ _ => RecType(n, Bind(alpha, t))
    }
  }

  lazy val refinementType: Parser[Tree] = {
    (lbra ~ variable ~ colon ~ typeExpr ~ comma ~ expression ~ rbra).map {
      case _ ~ Var(x) ~ _ ~ ty ~ _ ~ p ~ _ => RefinementType(ty, Bind(x, p))
    }
  }

  lazy val operatorType: Parser[Tree] = {
    operators(simpleTypeExpr)(
      sumType is LeftAssociative,
      piType is RightAssociative
    )
  }

  lazy val simpleTypeExpr = basicType | recType | refinementType | variable

  lazy val typeExpr: Parser[Tree] = recursive {
    operatorType
  }



  val boolean = accept(BooleanClass) { case BooleanToken(value, _) => BoolLiteral(value) }
  val number = accept(NumberClass) { case NumberToken(value, _) => NatLiteral(value) }
  val variable = accept(VarClass) { case VarToken(content, _) => Var(Identifier(0, content)) }
  val unit = accept(UnitClass) { case _ => UnitLiteral }

  val string = accept(StringClass) { case StringToken(content, _) => content }

  val literal = variable | number | boolean | unit

  def binopParser(op: Operator) = {
    accept(OperatorClass(op)) {
    case s =>
      val f: (Tree, Tree) => Tree = (x: Tree, y: Tree) => Primitive(op, List(x, y))
      f
    }
  }

  def unopParser(op: Operator) = {
    accept(OperatorClass(op)) {
    case s =>
      val f: Tree => Tree = (x: Tree) => Primitive(op, List(x))
      f
    }
  }

  val plus = binopParser(Plus)
  val minus = binopParser(Minus)
  val mul = binopParser(Mul)
  val div = binopParser(Div)

  val and = binopParser(And)
  val or = binopParser(Or)
  val not = unopParser(Not)

  val eq = binopParser(Eq)
  val neq = binopParser(Neq)
  val lt = binopParser(Lt)
  val gt = binopParser(Gt)
  val lteq = binopParser(Lteq)
  val gteq = binopParser(Gteq)

  lazy val function: Parser[Tree] = {
    (funK ~ lpar ~ variable ~ colon ~ typeExpr ~ rpar ~ arrow ~ bracketExpr).map {
      case _ ~ _ ~ Var(x) ~ _ ~ tp ~ _ ~ _ ~ e => Lambda(stainlessSome(tp), Bind(x, e))
    }
  }

  def buildFix(name: Identifier, body: Tree, bodyType: Tree) = {
    Fix(
      stainlessNone(),
      Bind(
        Identifier(0, "_"),
        Bind(
          name,
          Tree.replace(name, App(Var(name), UnitLiteral), body)
        )
      )
    )
  }

  def foldArgs(args: Seq[(Identifier, Tree)], body: Tree): Tree = {
    args.foldRight(body) {
      case ((x, ty1), acc) => Lambda(stainlessSome(ty1), Bind(x, acc))
    }
  }

  lazy val defFunction: Parser[Tree] = recursive {
    (defK ~ variable ~ lpar ~ repsep(variable ~ colon ~ typeExpr, comma) ~ rpar ~
    opt(colon ~ typeExpr) ~ assignation ~ bracketExpr ~ opt(expression)).map {
      case _ ~ Var(f) ~ _ ~ argsT ~ _ ~ rt ~ _ ~ e1 ~ e2 =>
        val args = argsT.map { case (Var(x) ~ _ ~ t) => (x, t) }
        val body = if(args.isEmpty) Lambda(stainlessSome(UnitType), Bind(Identifier(0, "_"), e1)) else foldArgs(args, e1)
        val funExpr = body
        e2 match {
          case None => LetIn(stainlessNone(), funExpr, Bind(f, Var(f)))
          case Some(e) => LetIn(stainlessNone(), funExpr, Bind(f, e))
        }
    }
  }

  lazy val error: Parser[Tree] = {
    (errorK ~ opt(lsbra ~ typeExpr ~ rsbra) ~ lpar ~ string ~ rpar).map {
      case _ ~ tpe ~ _ ~ s ~ _ => tpe match {
        case None => ErrorTree(s, stainlessNone())
        case Some(_ ~ tp ~ _) => ErrorTree(s, stainlessSome(tp))
      }
    }
  }

  /*lazy val fixdefFunction: Parser[Tree] = recursive {
    (fixdefK ~ variable ~ lpar ~ variable ~ colone ~ typeExpr ~ comma ~ repsep(variable ~ colon ~ typeExpr, comma) ~ rpar ~
    colon ~ typeExpr ~ assignation ~ bracketExpr ~ opt(expression)).map {
      case _ ~ Var(f) ~ _ ~ argsT ~ _ ~ _ ~ rt ~ _ ~ e1 ~ e2 =>
        val args = argsT.map { case (Var(x) ~ _ ~ t) => (x, t) }
        val (body, bType) = if(args.isEmpty) (e1, rt) else foldArgs(args, e1, rt)
        val funExpr = if(appearFreeIn(Var(f), body)) buildFix(f, body, bType) else body
        e2 match {
          case None => LetIn(stainlessNone(), funExpr, Bind(f, Var(f)))
          case Some(e) => LetIn(stainlessNone(), funExpr, Bind(f, e))
        }
    }
  }*/

  lazy val fixpoint: Parser[Tree] = recursive {
    (fixK ~ opt(lsbra ~ variable ~ arrow ~ typeExpr ~ rsbra) ~
    lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ None ~ _ ~ Var(x) ~ _ ~ e ~ _ =>
        //println(s"WARNING : We won't be able to typechecks the fixpoint ${x} without type annotation.")
        val body = Tree.replace(x, App(Var(x), UnitLiteral), e)
        Fix(stainlessNone(), Bind(Identifier(0, "_"), Bind(x, body)))
      case _ ~ Some(_ ~ Var(n) ~ _ ~ tp ~ _) ~ _ ~ Var(x) ~ _ ~ e ~ _ =>
        val body = Tree.replace(
          x,
          Inst(
            App(Var(x), UnitLiteral),
            Primitive(Minus, List(Var(n), NatLiteral(1)))
          ),
          e
        )
        Fix(stainlessSome(Bind(n, tp)), Bind(n, Bind(x, body)))
    }
  }

  lazy val fold: Parser[Tree] = recursive {
    (foldK ~ opt(lsbra ~ typeExpr ~ rsbra) ~
    lpar ~ expression ~ rpar).map {
      case _ ~ None ~ _ ~ e ~ _  =>
        //println(s"WARNING : We won't be able to typechecks the Fold ${e} without type annotation.\n")
        Fold(stainlessNone(), e)
      case _ ~ Some(_ ~ tp ~ _) ~ _ ~ e ~ _ => Fold(stainlessSome(tp), e)
    }
  }

  lazy val unfold: Parser[Tree] = recursive {
    (unfoldK ~ lpar ~ expression ~ rpar ~ inK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ ~ _ ~ _ ~ Var(x) ~ _ ~ f ~ _ => Unfold(e, Bind(x, f))
    }
  }

  lazy val letIn: Parser[Tree] = recursive {
    (valK ~ variable ~ opt(colon ~ typeExpr) ~ assignation ~ expression ~ inK ~ expression).map {
      case _ ~ Var(x) ~ None ~ _ ~ e ~ _ ~ e2 =>
        LetIn(stainlessNone(), e, Bind(x, e2))
      case _ ~ Var(x) ~ Some(_ ~ tp) ~ _ ~ e ~ _ ~ e2 =>
        LetIn(stainlessSome(tp), e, Bind(x, e2))
    }
  }

  lazy val parExpr: Parser[Tree] = {
    (lpar ~ repsep(expression, comma) ~ rpar).map {
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

  lazy val application: Parser[Tree] = recursive {
    (simpleExpr ~ many(simpleExpr)).map {
      case f ~ args => args.reverse.foldRight(f) {case (e, acc) => App(acc, e) }
    }
  }

  lazy val eitherMatch: Parser[Tree] = recursive {
    (matchK ~ expression ~ lbra ~
    caseK ~ leftK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    caseK ~ rightK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    rbra).map {
      case (_ ~ e ~ _ ~ _ ~ _ ~ _ ~ Var(v1) ~ _ ~ _ ~ e1 ~
      _ ~ _ ~ _ ~ Var(v2) ~ _ ~ _ ~ e2 ~ _) =>
      EitherMatch(e, Bind(v1, e1), Bind(v2, e2))
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

  lazy val first: Parser[Tree] = recursive {
    (firstK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => First(e)
    }
  }

  lazy val second: Parser[Tree] = recursive {
    (secondK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => Second(e)
    }
  }

  lazy val instantiate: Parser[Tree] = recursive {
    (instK ~ lpar ~ expression ~ comma ~ expression ~ rpar).map {
      case _ ~ _ ~ f ~ _ ~ e ~ _ => Inst(f, e)
    }
  }

  val operator: Parser[Tree] = {
    operators(prefixes(not, application))(
      mul | div | and is LeftAssociative,
      plus | minus | or is LeftAssociative,
      lt | gt | lteq | gteq is LeftAssociative,
      eq is LeftAssociative)
  }

  lazy val condition: Parser[Tree] = {
    (ifK ~ lpar ~ expression ~ rpar ~ optBracketExpr ~ elseK ~ optBracketExpr).map {
      case _ ~ _ ~ cond ~ _ ~ vTrue ~ _ ~ vFalse => IfThenElse(cond, vTrue, vFalse)
    }
  }

  lazy val optBracketExpr: Parser[Tree] = expression | bracketExpr

  lazy val bracketExpr: Parser[Tree] = {
    (lbra ~ expression ~ rbra).map { case _ ~ e ~ _ => e }
  }

  lazy val simpleExpr: Parser[Tree] = literal | parExpr | fixpoint | function | left | right | first | second |
    error | instantiate | fold | unfold

  lazy val expression: Parser[Tree] = recursive {
    condition | eitherMatch | letIn | defFunction | operator
  }



  def apply(it: Iterator[Token]): ParseResult[Tree] = expression(it)
}