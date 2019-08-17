package parser

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

import trees._

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

  val lexer = Lexer(
    // Operators
    oneOf("-+/*!<>") | word("&&") |  word("||") |
    word("==") | word("!=") |word("<=") | word(">=")
    |> { (cs, r) => OperatorToken(Operator.fromString(cs.mkString), r) },

    //Assignation
    oneOf("=")
      |> { (cs, r) => AssignationToken(r) },

    /*word("")
      |> { (cs, r) => UnitToken(r) },*/


    // Separator
    word("{{") | word("}}") | oneOf("{},().:[]") | word("=>")
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
    word("Unfold") | word("UnfoldPositive") | word("Decreases") | word("Pi") | word("Sigma") | word("Forall") | word("Lambda")
      |> { (cs, r) => KeyWordToken(cs.mkString, r) },

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

  val assignation: Syntax[Token] = elem(AssignationClass)
  val lpar: Syntax[Token] = elem(SeparatorClass("("))
  val rpar: Syntax[Token] = elem(SeparatorClass(")"))
  val lbra: Syntax[Token] = elem(SeparatorClass("{"))
  val rbra: Syntax[Token] = elem(SeparatorClass("}"))
  val dlbra: Syntax[Token] = elem(SeparatorClass("{{"))
  val drbra: Syntax[Token] = elem(SeparatorClass("}}"))
  val lsbra: Syntax[Token] = elem(SeparatorClass("["))
  val rsbra: Syntax[Token] = elem(SeparatorClass("]"))
  val comma: Syntax[Token] = elem(SeparatorClass(","))
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
  val valK: Syntax[Token] = elem(KeyWordClass("val"))
  val defK: Syntax[Token] = elem(KeyWordClass("def"))
  val recK: Syntax[Token] = elem(TypeClass("Rec"))
  val errorK: Syntax[Token] = elem(KeyWordClass("Error"))
  val instK: Syntax[Token] = elem(KeyWordClass("Inst"))
  val fixdefK: Syntax[Token] = elem(KeyWordClass("fixdef"))
  val foldK: Syntax[Token] = elem(KeyWordClass("Fold"))
  val unfoldK: Syntax[Token] = elem(KeyWordClass("Unfold"))
  val unfoldPositiveK: Syntax[Token] = elem(KeyWordClass("UnfoldPositive"))
  val decreasesK: Syntax[Token] = elem(KeyWordClass("Decreases"))
  val piK: Syntax[Token] = elem(KeyWordClass("Pi"))
  val sigmaK: Syntax[Token] = elem(KeyWordClass("Sigma"))
  val forallK: Syntax[Token] = elem(KeyWordClass("Forall"))
  val lambdaK: Syntax[Token] = elem(KeyWordClass("Lambda"))

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
    (lbra ~ variable ~ colon ~ typeExpr ~ comma ~ expression ~ rbra).map {
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



  val boolean: Syntax[Tree] = accept(BooleanClass) { case BooleanToken(value, _) => BoolLiteral(value) }
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

  lazy val varTypeDef: Syntax[(Identifier, Tree)] = {
    (lpar ~ variable ~ colon ~ typeExpr ~ rpar).map {
      case _ ~ Var(v) ~ _ ~ ty ~ _ => (v, ty)
    }
  }

  lazy val sBracketArg: Syntax[(Identifier, Tree)] = {
    (lsbra ~ variable ~ rsbra).map { case _ ~ Var(v) ~ _ => (v, Abs(UnitLiteral)) }
  }

  lazy val bracketArg: Syntax[(Identifier, Tree)] = {
    (dlbra ~ variable ~ drbra).map { case _ ~ Var(v) ~ _ => (v, Ghost(UnitLiteral)) }
  }

  lazy val parArg: Syntax[(Identifier, Tree)] = {
    (lpar ~ variable ~ colon ~ typeExpr ~ rpar).map {
      case _ ~ Var(v) ~ _ ~ ty ~ _ => (v, ty)
    }
  }


  def defType(args: Seq[(Identifier, Tree)], retType: Tree): Tree = {
    args.foldRight(retType: Tree) {
      case ((id: Identifier, Abs(t)), acc) => PolyForallType(Bind(id, acc))
      case ((id, Ghost(_)), acc)           => PolyForallType(Bind(id, acc))
      case ((id, ty), acc)                 => PiType(ty, Bind(id, acc))
    }
  }

  def createFun(args: Seq[(Identifier, Tree)], body: Tree): Tree = {
    args.foldRight(body) {
      case ((id: Identifier, Abs(_)), acc) => Abs(Bind(id, acc))
      case ((id, Inst(_, _)), acc) => Ghost(Bind(id, acc))
      case ((id, ty), acc)         => Lambda(stainlessSome(ty), Bind(id, acc))
    }
  }

  def createApp(args: Seq[(Tree, Tree)], fun: Tree): Tree = {
    args.foldLeft(fun) {
      case (acc, (id, Abs(_)))   => TypeApp(acc, stainlessSome(id))
      case (acc, (id, Ghost(_))) => Inst(acc, id)
      case (acc, (id, ty))       => App(acc, id)
    }
  }

  lazy val argument: Syntax[(Identifier, Tree)] = sBracketArg | bracketArg | parArg

  lazy val defFunction: Syntax[Tree] = recursive {
    (defK ~ variable ~ many1(argument) ~ opt(retTypeP) ~ assignation ~ lbra ~ opt(measureP) ~
    expression ~ rbra ~ opt(expression)).map {
      case _ ~ Var(f) ~ args ~ retType ~ _ ~ _ ~ measure ~ e1 ~ _ ~ e2 =>
        val followingExpr = e2.getOrElse(Var(f))
        (measure, retType) match {
          case (Some(_), None) =>
            throw new java.lang.Exception(s"Recursive function $f needs return type.")
          case (None, None) =>
            LetIn(stainlessNone(), createFun(args, e1), Bind(f, followingExpr))
          case (None, Some(ty)) =>
            if(f.isFreeIn(e1)) throw new java.lang.Exception(s"Recursive function $f needs a measure.")
            LetIn(stainlessSome(defType(args, ty)), createFun(args, e1), Bind(f, followingExpr))
          case (Some(measure), Some(ty)) =>
            val n = Identifier(0, "_n")
            val expr = e1.replace(f,
              Inst(App(Var(f), UnitLiteral),
                Primitive(Minus, List(Var(n), NatLiteral(1)))
              )
            )
            val reverseArgs = args.reverse.toList
            val (x, xTy) = reverseArgs.head
            val refinedArgs = ((x, RefinementType(xTy, Bind(x, Primitive(Lteq, List(measure, Var(n)))))) :: reverseArgs.tail).reverse
            val fun = createFun(refinedArgs, expr)
            val funTy = defType(refinedArgs, ty)
            val fix = Fix(stainlessSome(Bind(n, funTy)), Bind(n, Bind(f, fun)))

            val instBody = createApp(args.map { case (id, t) => (Var(id), t) }, Inst(Var(f), Primitive(Plus, List(measure, NatLiteral(1)))))
            val instFun = createFun(args, instBody)
            val complete = LetIn(stainlessNone(), fix, Bind(f, instFun))
            LetIn(stainlessNone(), complete, Bind(f, followingExpr))
        }
    }
  }

  lazy val retTypeP: Syntax[Tree] = { (colon ~ typeExpr).map { case _ ~ t => t } }
  lazy val measureP: Syntax[Tree] = { (decreasesK ~ lpar ~ expression ~rpar).map { case _ ~ _ ~ e ~ _ => e } }


  lazy val function: Syntax[Tree] = {
    (funK ~ many(argument) ~ arrow ~ bracketExpr).map {
      case _ ~ args ~ _ ~ e => createFun(args, e)
    }
  }

  lazy val string: Syntax[String] = accept(StringClass) { case StringToken(content, _) => content }

  lazy val error: Syntax[Tree] = {
    (errorK ~ opt(lsbra ~ typeExpr ~ rsbra) ~ lpar ~ string ~ rpar).map {
      case _ ~ tpe ~ _ ~ s ~ _ => tpe match {
        case None => ErrorTree(s, stainlessNone())
        case Some(_ ~ tp ~ _) => ErrorTree(s, stainlessSome(tp))
      }
    }
  }

  lazy val fixpoint: Syntax[Tree] = recursive {
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

  lazy val fold: Syntax[Tree] = recursive {
    (foldK ~ opt(lsbra ~ typeExpr ~ rsbra) ~
    lpar ~ expression ~ rpar).map {
      case _ ~ None ~ _ ~ e ~ _  =>
        //println(s"WARNING : We won't be able to typechecks the Fold ${e} without type annotation.\n")
        Fold(stainlessNone(), e)
      case _ ~ Some(_ ~ tp ~ _) ~ _ ~ e ~ _ => Fold(stainlessSome(tp), e)
    }
  }

  lazy val unfold: Syntax[Tree] = recursive {
    (unfoldK ~ lpar ~ expression ~ rpar ~ inK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ ~ _ ~ _ ~ Var(x) ~ _ ~ f ~ _ => Unfold(e, Bind(x, f))
    }
  }

  lazy val unfoldPositive: Syntax[Tree] = recursive {
    (unfoldPositiveK ~ lpar ~ expression ~ rpar ~ inK ~ lpar ~ variable ~ arrow ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ ~ _ ~ _ ~ Var(x) ~ _ ~ f ~ _ => UnfoldPositive(e, Bind(x, f))
    }
  }

  lazy val letIn: Syntax[Tree] = recursive {
    (valK ~ variable ~ opt(colon ~ typeExpr) ~ assignation ~ expression ~ inK ~ expression).map {
      case _ ~ Var(x) ~ None ~ _ ~ e ~ _ ~ e2 =>
        LetIn(stainlessNone(), e, Bind(x, e2))
      case _ ~ Var(x) ~ Some(_ ~ tp) ~ _ ~ e ~ _ ~ e2 =>
        LetIn(stainlessSome(tp), e, Bind(x, e2))
    }
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

  /*lazy val sBracketType: Syntax[Tree] = {
    (lsbra ~ typeExpr ~ rsbra).map { case _ ~ e ~ _ => e }
  }

  lazy val application: Syntax[Tree] = recursive {
    (simpleExpr ~ many(sBracketType) ~ many(simpleExpr)).map {
      case f ~ typeArgs ~ args =>
        args.foldLeft(
          typeArgs.foldLeft(f) { case (acc: Tree, e) => TypeApp(acc, stainlessSome(e)) }
        ) { case (acc, e) => App(acc, e) }
    }
  }*/


  lazy val sBracketAppArg: Syntax[(Tree, Tree)] = {
    (lsbra ~ typeExpr ~ rsbra).map { case _ ~ e ~ _ => (e, Abs(UnitLiteral)) }
  }

  lazy val bracketAppArg: Syntax[(Tree, Tree)] = {
    (dlbra ~ expression ~ drbra).map { case _ ~ ty ~ _ => (ty, Ghost(UnitLiteral)) }
  }

  lazy val parAppArg: Syntax[(Tree, Tree)] = {
    (simpleExpr).map { case e => (e, UnitLiteral)
    }
  }

  lazy val appArg: Syntax[(Tree, Tree)] = parAppArg | bracketAppArg | sBracketAppArg

  lazy val application: Syntax[Tree] = {
    (simpleExpr ~ many(appArg)).map { case f ~ args => createApp(args, f) }
  }

  lazy val eitherMatch: Syntax[Tree] = recursive {
    (matchK ~ expression ~ lbra ~
    caseK ~ leftK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    caseK ~ rightK ~ lpar ~ variable ~ rpar ~ arrow ~ optBracketExpr ~
    rbra).map {
      case (_ ~ e ~ _ ~ _ ~ _ ~ _ ~ Var(v1) ~ _ ~ _ ~ e1 ~
      _ ~ _ ~ _ ~ Var(v2) ~ _ ~ _ ~ e2 ~ _) =>
      EitherMatch(e, Bind(v1, e1), Bind(v2, e2))
    }
  }

  lazy val left: Syntax[Tree] = recursive {
    (leftK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => LeftTree(e)
    }
  }

  lazy val right: Syntax[Tree] = recursive {
    (rightK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => RightTree(e)
    }
  }

  lazy val first: Syntax[Tree] = recursive {
    (firstK ~ lpar ~ expression ~ rpar).map {
      case _ ~ _ ~ e ~ _ => First(e)
    }
  }

  lazy val second: Syntax[Tree] = recursive {
    (secondK ~ lpar ~ expression ~ rpar).map {
      case  _ ~ _ ~ e ~ _ => Second(e)
    }
  }

  lazy val instantiate: Syntax[Tree] = recursive {
    (instK ~ lpar ~ expression ~ comma ~ expression ~ rpar).map {
      case _ ~ _ ~ f ~ _ ~ e ~ _ => Inst(f, e)
    }
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
      case (x, op, y) => Primitive(Operator.fromString(op), List(x,y))
    }, {
      case Primitive(op, Cons(x, Cons(y, Nil()))) => (x, op.toString, y)
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
    error | instantiate | fold | unfold | unfoldPositive | lambdaAbs

  lazy val expression: Syntax[Tree] = recursive {
    condition | eitherMatch | letIn | defFunction | operator
  }

  def apply(it: Iterator[Token]): ParseResult[Tree] = expression(it)
}
