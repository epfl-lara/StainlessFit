/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package trees

import util.RunContext
import parser.FitParser

sealed abstract class Operator {
  def isNatToNatBinOp: Boolean = Operator.isNatToNatBinOp(this)
  def isNatToBoolBinOp: Boolean = Operator.isNatToBoolBinOp(this)
  def isNatBinOp: Boolean = Operator.isNatBinOp(this)
  def isBoolToBoolBinOp: Boolean = Operator.isBoolToBoolBinOp(this)
  def isBoolToBoolUnOp: Boolean = Operator.isBoolToBoolUnOp(this)
  def returnedType: Tree = Operator.returnedType(this)
  def operandsType: Tree = Operator.operandsType(this)
  def isBinOp: Boolean = Operator.isBinOp(this)
  def isUnOp: Boolean = Operator.isUnOp(this)
}

case object Not extends Operator {
  override def toString = "!"
}
case object And extends Operator {
  override def toString = "&&"
}
case object Or extends Operator {
  override def toString = "||"
}

case object Cup extends Operator {
  override def toString = "∪"
}

case object Plus extends Operator {
  override def toString = "+"
}
case object Minus extends Operator {
  override def toString = "-"
}
case object Mul extends Operator {
  override def toString = "*"
}
case object Div extends Operator {
  override def toString = "/"
}

case object Eq extends Operator {
  override def toString = "=="
}
case object Neq extends Operator {
  override def toString = "!="
}
case object Leq extends Operator {
  override def toString = "<="
}
case object Geq extends Operator {
  override def toString = ">="
}
case object Lt extends Operator {
  override def toString = "<"
}
case object Gt extends Operator {
  override def toString = ">"
}

case object Nop extends Operator {
  override def toString = "Nop"
}


object Operator {
  def isNatToNatBinOp(op: Operator): Boolean = {
    op match {
      case Plus => true
      case Minus => true
      case Mul => true
      case Div => true
      case _ => false
    }
  }

  def isNatToBoolBinOp(op: Operator): Boolean = {
    op match {
      case Eq => true
      case Neq => true
      case Leq => true
      case Geq => true
      case Lt => true
      case Gt => true
      case _ => false
    }
  }

  def isNatBinOp(op: Operator): Boolean = {
    isNatToNatBinOp(op) || isNatToBoolBinOp(op)
  }

  def isBoolToBoolBinOp(op: Operator): Boolean = {
    op match {
      case And => true
      case Or => true
      case _ => false
    }
  }

  def isBoolToBoolUnOp(op: Operator): Boolean = {
    op match {
      case Not => true
      case _ => false
    }
  }

  def isBinOp(op: Operator): Boolean = {
    isNatBinOp(op) || isBoolToBoolBinOp(op)
  }

  def isUnOp(op: Operator): Boolean = {
    isBoolToBoolUnOp(op)
  }

  def returnedType(op: Operator): Tree = {
    if (isNatToNatBinOp(op)) NatType
    else if (isNatToBoolBinOp(op)) BoolType
    else if (isBoolToBoolBinOp(op)) BoolType
    else if (isBoolToBoolUnOp(op)) BoolType
    else BottomType
  }

  def operandsType(op: Operator): Tree = {
    if (isNatBinOp(op)) NatType
    else if (isBoolToBoolBinOp(op)) BoolType
    else if (isBoolToBoolUnOp(op)) BoolType
    else BottomType
  }

  def fromString(str: String): Option[Operator] = str match {
    case "!" => Some(Not)
    case "&&" => Some(And)
    case "||" => Some(Or)
    case "+" => Some(Plus)
    case "-" => Some(Minus)
    case "*" => Some(Mul)
    case "/" => Some(Div)
    case "==" => Some(Eq)
    case "!=" => Some(Neq)
    case "<=" => Some(Leq)
    case ">=" => Some(Geq)
    case "<" => Some(Lt)
    case ">" => Some(Gt)
    case _ => None
  }
}

object Tree {

  def replaceBind(bind: Tree, v: Tree)(implicit rc: RunContext): Tree = {
    require(isBind(bind))
    bind match {
      case Bind(id, body) => replace(id, v, body)
      case t => t
    }
  }

  def replace(id: Identifier, v: Tree, body: Tree)(implicit rc: RunContext): Tree = {
    body match {
      case Var(id2) if id2 == id => v
      case Var(_) => body
      case UnitLiteral => body
      case NatLiteral(_) => body
      case BooleanLiteral(_) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(replace(id, v, cond), replace(id, v, t1), replace(id, v, t2))
      case App(t1, t2) =>
        App(replace(id, v, t1), replace(id, v, t2))
      case Pair(t1, t2) => Pair(replace(id, v, t1), replace(id, v, t2))
      case Size(t) => Size(replace(id, v, t))
      case First(t) => First(replace(id, v, t))
      case Second(t) => Second(replace(id, v, t))
      case LeftTree(t) => LeftTree(replace(id, v, t))
      case RightTree(t) => RightTree(replace(id, v, t))
      case Because(t1, t2) => Because(replace(id, v, t1), replace(id, v, t2))
      case Bind(id2, e) if (id == id2) => body
      case Bind(id2, e) =>
        if (id2.isFreeIn(v))
          rc.reporter.fatalError(
            s"""Replacing ${Printer.asString(id)} by ${Printer.asString(v)} in
              |$body would capture variable ${Printer.asString(id2)}""".stripMargin
          )
        Bind(id2, replace(id, v, e))
      case Lambda(None, bind) => Lambda(None, replace(id, v, bind))
      case Lambda(Some(tp), bind) => Lambda(Some(replace(id, v, tp)), replace(id, v, bind))
      case ErasableLambda(tp, bind) => ErasableLambda(replace(id, v, tp), replace(id, v, bind))
      case Fix(None, bind) => Fix(None, replace(id, v, bind))
      case Fix(Some(tp), bind) => Fix(Some(replace(id, v, tp)), replace(id, v, bind))
      case LetIn(None, v1, bind) => LetIn(None, replace(id, v, v1), replace(id, v, bind))
      case LetIn(Some(tp), v1, bind) => LetIn(Some(replace(id, v, tp)), replace(id, v, v1), replace(id, v, bind))
      case MacroTypeDecl(tpe, bind) => MacroTypeDecl(replace(id, v, tpe), replace(id, v, bind))
      case MacroTypeInst(v1, args) =>
        MacroTypeInst(
          replace(id, v, v1),
          args.map(p => (p._1, replace(id, v, p._2)))
        )
      case NatMatch(t, t0, bind) => NatMatch(replace(id, v, t), replace(id, v, t0), replace(id, v, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replace(id, v, t), replace(id, v, bind1), replace(id, v, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replace(id, v, _)))
      case ErasableApp(t1, t2) => ErasableApp(replace(id, v, t1), replace(id, v, t2))
      case Fold(tp, t) => Fold(replace(id, v, tp), replace(id, v, t))
      case Unfold(t, bind) => Unfold(replace(id, v, t), replace(id, v, bind))
      case UnfoldPositive(t, bind) => UnfoldPositive(replace(id, v, t), replace(id, v, bind))
      case Abs(bind) => Abs(replace(id, v, bind))
      case TypeApp(abs, t) => TypeApp(replace(id, v, abs), replace(id, v, t))
      case Error(_, _) => body

      case NatType => body
      case BoolType => body
      case UnitType => body
      case SumType(t1, t2) => SumType(replace(id, v, t1), replace(id, v, t2))
      case PiType(t1, bind) => PiType(replace(id, v, t1), replace(id, v, bind))
      case SigmaType(t1, bind) => SigmaType(replace(id, v, t1), replace(id, v, bind))
      case IntersectionType(t1, bind) => IntersectionType(replace(id, v, t1), replace(id, v, bind))
      case ExistsType(t1, bind) => ExistsType(replace(id, v, t1), replace(id, v, bind))
      case RefinementType(t1, bind) => RefinementType(replace(id, v, t1), replace(id, v, bind))
      case RefinementByType(t1, bind) => RefinementByType(replace(id, v, t1), replace(id, v, bind))
      case EqualityType(t1, t2) => EqualityType(replace(id, v, t1), replace(id, v, t2))
      case RecType(n, bind) => RecType(replace(id, v, n), replace(id, v, bind))
      case PolyForallType(bind) => PolyForallType(replace(id, v, bind))
      case Node(name, children) => Node(name, children.map(replace(id, v, _)))

      case BottomType => BottomType
      case TopType => TopType
    }
  }

  def traverse(t: Tree, pre: Tree => Unit, post: Tree => Unit): Unit = {
    pre(t)
    t match {
      case Var(_) => ()
      case UnitLiteral => ()
      case NatLiteral(_) => ()
      case BooleanLiteral(_) => ()
      case IfThenElse(cond, t1, t2) =>
        traverse(cond, pre, post)
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case App(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case Pair(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case Size(t) => traverse(t, pre, post)
      case First(t) => traverse(t, pre, post)
      case Second(t) => traverse(t, pre, post)
      case LeftTree(t) => traverse(t, pre, post)
      case RightTree(t) => traverse(t, pre, post)
      case Because(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case Bind(id2, e) =>
        traverse(e, pre, post)
      case Lambda(optTy, bind) =>
        optTy.foreach(ty => traverse(ty, pre, post))
        traverse(bind, pre, post)
      case ErasableLambda(ty, bind) =>
        traverse(ty, pre, post)
        traverse(bind, pre, post)
      case Fix(optTy, bind) =>
        optTy.foreach(ty => traverse(ty, pre, post))
        traverse(bind, pre, post)
      case LetIn(optTy, t, bind) =>
        optTy.foreach(ty => traverse(ty, pre, post))
        traverse(t, pre, post)
        traverse(bind, pre, post)
      case MacroTypeDecl(ty, bind) =>
        traverse(ty, pre, post)
        traverse(bind, pre, post)
      case MacroTypeInst(v, args) =>
        traverse(v, pre, post)
        args.foreach(arg => traverse(arg._2, pre, post))
      case NatMatch(t, t0, bind) =>
        traverse(t, pre, post)
        traverse(t0, pre, post)
        traverse(bind, pre, post)
      case EitherMatch(t, bind1, bind2) =>
        traverse(t, pre, post)
        traverse(bind1, pre, post)
        traverse(bind2, pre, post)
      case Primitive(op, args) =>
        args.foreach(arg => traverse(arg, pre, post))
      case ErasableApp(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case Fold(tp, t) =>
        traverse(tp, pre, post)
        traverse(t, pre, post)
      case Unfold(t, bind) =>
        traverse(t, pre, post)
        traverse(bind, pre, post)
      case UnfoldPositive(t, bind) =>
        traverse(t, pre, post)
        traverse(bind, pre, post)
      case Abs(bind) =>
        traverse(bind, pre, post)
      case TypeApp(abs, t) =>
        traverse(abs, pre, post)
        traverse(t, pre, post)
      case Error(_, optTy) =>
        optTy.foreach(ty => traverse(ty, pre, post))

      case NatType => ()
      case BoolType => ()
      case UnitType => ()
      case SumType(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case PiType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case SigmaType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case UnionType(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case IntersectionType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case ExistsType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case RefinementType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case RefinementByType(t1, bind) =>
        traverse(t1, pre, post)
        traverse(bind, pre, post)
      case RecType(n, bind) =>
        traverse(n, pre, post)
        traverse(bind, pre, post)
      case PolyForallType(bind) =>
        traverse(bind, pre, post)
      case EqualityType(t1, t2) =>
        traverse(t1, pre, post)
        traverse(t2, pre, post)
      case Node(name, args) =>
        args.foreach(arg => traverse(arg, pre, post))

      case BottomType =>
      case TopType =>

      case _ => throw new java.lang.Exception(s"Function `traverse` is not implemented on $t (${t.getClass}).")
    }
    post(t)
  }

  def replace(p: Tree => Option[Either[String,Tree]], body: Tree, post: Tree => Unit): Either[String, Tree] = {
    val res = p(body).getOrElse(body match {
      case Var(_) => Right(body)
      case UnitLiteral => Right(body)
      case NatLiteral(_) => Right(body)
      case BooleanLiteral(_) => Right(body)
      case IfThenElse(cond, t1, t2) =>
        for (
          rcond <- replace(p,cond,post);
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
        IfThenElse(rcond, rt1, rt2)

      case App(t1, t2) =>
        for (
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
          App(rt1, rt2)

      case Pair(t1, t2) =>
        for (
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
          Pair(rt1, rt2)

      case Size(t) => replace(p, t,post).map(Size(_))
      case First(t) => replace(p, t,post).map(First(_))
      case Second(t) => replace(p, t,post).map(Second(_))
      case LeftTree(t) => replace(p, t,post).map(LeftTree(_))
      case RightTree(t) => replace(p, t,post).map(RightTree(_))
      case Because(t1, t2) =>
        for (
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
          Because(rt1, rt2)

      case Bind(id, t) => replace(p, t, post).map(Bind(id, _))
      case Lambda(None, bind) => replace(p, bind, post).map(Lambda(None, _))
      case Lambda(Some(tp), bind) =>
        for (
          rtp <- replace(p, tp, post);
          rbind <- replace(p, bind, post)
        ) yield
          Lambda(Some(rtp), rbind)

      case ErasableLambda(tp, bind) =>
        for (
          rtp <- replace(p, tp, post);
          rbind <- replace(p, bind, post)
        ) yield
          ErasableLambda(rtp, rbind)

      case Fix(None, bind) => replace(p, bind, post).map(Fix(None, _))
      case Fix(Some(tp), bind) =>
        for (
          rtp <- replace(p, tp, post);
          rbind <- replace(p, bind, post)
        ) yield
          Fix(Some(rtp), rbind)

      case LetIn(None, v1, bind) =>
        for (
          rv1 <- replace(p, v1, post);
          rbind <- replace(p, bind, post)
        ) yield
          LetIn(None, rv1, rbind)
      case LetIn(Some(tp), v1, bind) =>
        for (
          rtp <- replace(p, tp, post);
          rv1 <- replace(p, v1, post);
          rbind <- replace(p, bind, post)
        ) yield
          LetIn(Some(rtp), rv1, rbind)
      case MacroTypeDecl(tp, bind) =>
        for (
          rtp <- replace(p, tp, post);
          rbind <- replace(p, bind, post)
        ) yield
          MacroTypeDecl(rtp, rbind)
      case MacroTypeInst(v1, args) =>
        for(
          rv1 <- replace(p, v1, post);
          eithers = args.map(arg => replace(p, arg._2, post));
          rargs <- eithers.foldLeft(Right(Seq()): Either[String, Seq[Tree]]) {
            case (acc @ Left(_), _) => acc
            case (_, Left(error)) => Left(error)
            case (Right(acc), Right(rarg)) => Right(acc :+ rarg)
          }
        ) yield
          MacroTypeInst(rv1, args.map(_._1).zip(rargs))

      case NatMatch(t, t0, bind) =>
        for (
          rt <- replace(p, t, post);
          rt0 <- replace(p, t0, post);
          rbind <- replace(p, bind, post)
        ) yield
          NatMatch(rt, rt0, rbind)
      case EitherMatch(t, bind1, bind2) =>
        for (
          rt <- replace(p, t, post);
          rbind1 <- replace(p, bind1, post);
          rbind2 <- replace(p, bind2, post)
        ) yield
          EitherMatch(rt, rbind1, rbind2)
      case Primitive(op, args) =>
        val eithers = args.map(arg => replace(p, arg, post));
        for(
          rargs <- eithers.foldLeft(Right(Nil): Either[String, List[Tree]]) {
            case (acc @ Left(_), _) => acc
            case (_, Left(error)) => Left(error)
            case (Right(acc), Right(rarg)) => Right(acc :+ rarg)
          }
        ) yield
          Primitive(op, rargs)
      case Node(name, children) =>
        val eithers = children.map(arg => replace(p, arg, post));
        for(
          rargs <- eithers.foldLeft(Right(Nil): Either[String, List[Tree]]) {
            case (acc @ Left(_), _) => acc
            case (_, Left(error)) => Left(error)
            case (Right(acc), Right(rarg)) => Right(acc :+ rarg)
          }
        ) yield
          Node(name, rargs)
      case ErasableApp(t1, t2) =>
        for (
          rt1 <- replace(p,t1, post);
          rt2 <- replace(p,t2, post)
        ) yield
          ErasableApp(rt1, rt2)

      case Fold(tp, t) =>
        for (
          rtp <- replace(p, tp, post);
          rt <- replace(p, t, post)
        ) yield
          Fold(rtp, rt)
      case Unfold(t, bind) =>
        for (
          rt <- replace(p,t, post);
          rbind <- replace(p,bind, post)
        ) yield
          Unfold(rt, rbind)
      case UnfoldPositive(t, bind) =>
        for (
          rt <- replace(p,t, post);
          rbind <- replace(p,bind, post)
        ) yield
          UnfoldPositive(rt, rbind)

      case Abs(bind) => replace(p, bind, post).map(Abs(_))
      case TypeApp(abs, t) =>
        for (
          rabs <- replace(p,abs, post);
          rt <- replace(p,t, post)
        ) yield
          TypeApp(rabs, rt)

      case Error(_, _) => Right(body)

      case NatType => Right(body)
      case BoolType => Right(body)
      case UnitType => Right(body)
      case SumType(t1, t2) =>
        for (
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
          SumType(rt1, rt2)
      case PiType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          PiType(rt1, rbind)
      case SigmaType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          SigmaType(rt1, rbind)
      case IntersectionType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          IntersectionType(rt1, rbind)
      case ExistsType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          ExistsType(rt1, rbind)
      case RefinementType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          RefinementType(rt1, rbind)
      case RefinementByType(t1, bind) =>
        for (
          rt1 <- replace(p,t1,post);
          rbind <- replace(p,bind,post)
        ) yield
          RefinementByType(rt1, rbind)
      case RecType(n, bind) =>
        for (
          rn <- replace(p,n,post);
          rbind <- replace(p,bind,post)
        ) yield
          RecType(rn, rbind)
      case PolyForallType(bind) =>
        replace(p, bind, post).map(PolyForallType(_))

      case EqualityType(t1, t2) =>
        for (
          rt1 <- replace(p,t1,post);
          rt2 <- replace(p,t2,post)
        ) yield
          EqualityType(rt1, rt2)

      case BottomType => Right(body)
      case TopType => Right(body)

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $body (${body.getClass}).")
    })
    post(body)
    res
  }

  def preMap(p: Tree => Option[Tree], body: Tree)(implicit rc: RunContext): Tree = {
    p(body) match {
      case Some(e) => preMap(p, e)
      case None => body match {
        case Var(_) => body
        case UnitLiteral => body
        case NatLiteral(_) => body
        case BooleanLiteral(_) => body
        case IfThenElse(cond, t1, t2) =>
          IfThenElse(preMap(p, cond), preMap(p, t1), preMap(p, t2))
        case App(t1, t2) =>
          App(preMap(p, t1), preMap(p, t2))
        case Pair(t1, t2) => Pair(preMap(p, t1), preMap(p, t2))
        case Size(t) => Size(preMap(p, t))
        case First(t) => First(preMap(p, t))
        case Second(t) => Second(preMap(p, t))
        case LeftTree(t) => LeftTree(preMap(p, t))
        case RightTree(t) => RightTree(preMap(p, t))
        case Because(t1, t2) => Because(preMap(p, t1), preMap(p, t2))
        case Bind(id2, e) => Bind(id2, preMap(p, e))
        case Lambda(None, bind) => Lambda(None, preMap(p, bind))
        case Lambda(Some(tp), bind) => Lambda(Some(preMap(p, tp)), preMap(p, bind))
        case ErasableLambda(tp, bind) => ErasableLambda(preMap(p, tp), preMap(p, bind))
        case Fix(None, bind) => Fix(None, preMap(p, bind))
        case Fix(Some(tp), bind) => Fix(Some(preMap(p, tp)), preMap(p, bind))
        case LetIn(None, v1, bind) => LetIn(None, preMap(p, v1), preMap(p, bind))
        case LetIn(Some(tp), v1, bind) => LetIn(Some(preMap(p, tp)), preMap(p, v1), preMap(p, bind))
        case MacroTypeDecl(tpe, bind) => MacroTypeDecl(preMap(p, tpe), preMap(p, bind))
        case MacroTypeInst(v1, args) =>
          MacroTypeInst(
            preMap(p, v1),
            args.map(a => (a._1, preMap(p, a._2)))
          )
        case NatMatch(t, t0, bind) => NatMatch(preMap(p, t), preMap(p, t0), preMap(p, bind))
        case EitherMatch(t, bind1, bind2) => EitherMatch(preMap(p, t), preMap(p, bind1), preMap(p, bind2))
        case Primitive(op, args) => Primitive(op, args.map(preMap(p, _)))
        case ErasableApp(t1, t2) => ErasableApp(preMap(p, t1), preMap(p, t2))
        case Fold(tp, t) => Fold(preMap(p, tp), preMap(p, t))
        case Unfold(t, bind) => Unfold(preMap(p, t), preMap(p, bind))
        case UnfoldPositive(t, bind) => UnfoldPositive(preMap(p, t), preMap(p, bind))
        case Abs(bind) => Abs(preMap(p, bind))
        case TypeApp(abs, t) => TypeApp(preMap(p, abs), preMap(p, t))
        case Error(_, _) => body

        case NatType => body
        case BoolType => body
        case UnitType => body
        case SumType(t1, t2) => SumType(preMap(p, t1), preMap(p, t2))
        case PiType(t1, bind) => PiType(preMap(p, t1), preMap(p, bind))
        case SigmaType(t1, bind) => SigmaType(preMap(p, t1), preMap(p, bind))
        case IntersectionType(t1, bind) => IntersectionType(preMap(p, t1), preMap(p, bind))
        case ExistsType(t1, bind) => ExistsType(preMap(p, t1), preMap(p, bind))
        case RefinementType(t1, bind) => RefinementType(preMap(p, t1), preMap(p, bind))
        case RefinementByType(t1, bind) => RefinementByType(preMap(p, t1), preMap(p, bind))
        case RecType(n, bind) => RecType(preMap(p, n), preMap(p, bind))
        case PolyForallType(bind) => PolyForallType(preMap(p, bind))
        case EqualityType(t1, t2) => EqualityType(preMap(p, t1), preMap(p, t2))
        case Node(name, children) => Node(name, children.map(preMap(p, _)))

        case BottomType => BottomType
        case TopType => TopType

        case _ => rc.reporter.fatalError(s"Function `preMap` is not implemented on $body (${body.getClass}).")
      }
    }
  }

  def postMap(p: Tree => Tree => Tree, body: Tree): Tree = {
    val resultTransformer = p(body)
    val res = body match {
      case Var(_) => body
      case UnitLiteral => body
      case NatLiteral(_) => body
      case BooleanLiteral(_) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(postMap(p, cond), postMap(p, t1), postMap(p, t2))
      case App(t1, t2) =>
        App(postMap(p, t1), postMap(p, t2))
      case Pair(t1, t2) => Pair(postMap(p, t1), postMap(p, t2))
      case Size(t) => Size(postMap(p, t))
      case First(t) => First(postMap(p, t))
      case Second(t) => Second(postMap(p, t))
      case LeftTree(t) => LeftTree(postMap(p, t))
      case RightTree(t) => RightTree(postMap(p, t))
      case Because(t1, t2) => Because(postMap(p, t1), postMap(p, t2))
      case Bind(id2, e) => Bind(id2, postMap(p, e))
      case Lambda(None, bind) => Lambda(None, postMap(p, bind))
      case Lambda(Some(tp), bind) => Lambda(Some(postMap(p, tp)), postMap(p, bind))
      case ErasableLambda(tp, bind) => ErasableLambda(postMap(p, tp), postMap(p, bind))
      case Fix(None, bind) => Fix(None, postMap(p, bind))
      case Fix(Some(tp), bind) => Fix(Some(postMap(p, tp)), postMap(p, bind))
      case LetIn(None, v1, bind) => LetIn(None, postMap(p, v1), postMap(p, bind))
      case LetIn(Some(tp), v1, bind) => LetIn(Some(postMap(p, tp)), postMap(p, v1),postMap(p, bind))
      case MacroTypeDecl(tpe, bind) => MacroTypeDecl(postMap(p, tpe), postMap(p, bind))
      case MacroTypeInst(v1, args) =>
        MacroTypeInst(
          postMap(p, v1),
          args.map(a => (a._1, postMap(p, a._2)))
        )
      case NatMatch(t, t0, bind) => NatMatch(postMap(p, t), postMap(p, t0), postMap(p, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(postMap(p, t), postMap(p, bind1), postMap(p, bind2))
      case Primitive(op, args) => Primitive(op, args.map(postMap(p, _)))
      case ErasableApp(t1, t2) => ErasableApp(postMap(p, t1), postMap(p, t2))
      case Fold(tp, t) => Fold(postMap(p, tp), postMap(p, t))
      case Unfold(t, bind) => Unfold(postMap(p, t), postMap(p, bind))
      case UnfoldPositive(t, bind) => UnfoldPositive(postMap(p, t), postMap(p, bind))
      case Abs(bind) => Abs(postMap(p, bind))
      case TypeApp(abs, t)=> TypeApp(postMap(p, abs), postMap(p, t))
      case Error(_, _) => body

      case NatType => body
      case BoolType => body
      case UnitType => body
      case SumType(t1, t2) => SumType(postMap(p, t1), postMap(p, t2))
      case PiType(t1, bind) => PiType(postMap(p, t1), postMap(p, bind))
      case SigmaType(t1, bind) => SigmaType(postMap(p, t1), postMap(p, bind))
      case IntersectionType(t1, bind) => IntersectionType(postMap(p, t1), postMap(p, bind))
      case ExistsType(t1, bind) => ExistsType(postMap(p, t1), postMap(p, bind))
      case RefinementType(t1, bind) => RefinementType(postMap(p, t1), postMap(p, bind))
      case RefinementByType(t1, bind) => RefinementByType(postMap(p, t1),postMap(p, bind))
      case RecType(n, bind) => RecType(postMap(p, n), postMap(p, bind))
      case PolyForallType(bind) => PolyForallType(postMap(p, bind))
      case EqualityType(t1, t2) => EqualityType(postMap(p, t1), postMap(p, t2))
      case Node(name, children) => Node(name, children.map(postMap(p, _)))

      case BottomType => BottomType
      case TopType => TopType

      case _ => throw new java.lang.Exception(s"Function `postMap` is not implemented on $body (${body.getClass}).")
    }
    resultTransformer(res)
  }

  def isError(e: Tree): Boolean = {
    e match {
      case Error(_, _) => true
      case _ => false
    }
  }

  def isValue(e: Tree): Boolean = {
    e match {
      case UnitLiteral => true
      case NatLiteral(_) => true
      case BooleanLiteral(_) => true
      case Lambda(_, _) => true
      case Pair(t1, t2) => isValue(t1) && isValue(t2)
      case RightTree(t) => isValue(t)
      case LeftTree(t) => isValue(t)
      case _ => false
    }
  }

  def isBind(t: Tree): Boolean = t.isInstanceOf[Bind]

  trait Solver {
    def targets: Map[Identifier, Option[Tree]]
    def recordSolution(x: Identifier, t: Tree): Unit
    def addTarget(x: Identifier): Unit
  }
  object Solver {
    implicit val defaultSolver: Solver = null
    def targets(x: Identifier)(implicit solver: Solver) =
      if (solver ne null) solver.targets.contains(x) else false
  }

  def areEqual(t1: Tree, t2: Tree)(implicit rc: RunContext, solver: Solver): Boolean = {
    (t1, t2) match {
      case (IfThenElse(cond1, t11, t12), IfThenElse(cond2, t21, t22)) =>
        areEqual(cond1, cond2) && areEqual(t11, t21) && areEqual(t12, t22)
      case (App(t11, t12), App(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Pair(t11, t12), Pair(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (First(t1), First(t2)) => areEqual(t1, t2)
      case (Second(t1), Second(t2)) => areEqual(t1, t2)
      case (LeftTree(t1), LeftTree(t2)) => areEqual(t1, t2)
      case (RightTree(t1), RightTree(t2)) => areEqual(t1, t2)
      case (Because(t11, t12), Because(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Bind(x1, t1), Bind(x2, t2)) => areEqual(t1, t2.replace(x2, Var(x1)))
      case (Lambda(None, bind1), Lambda(None, bind2)) => areEqual(bind1, bind2)
      case (Lambda(Some(tp1), bind1), Lambda(Some(tp2), bind2)) => areEqual(tp1, tp2) && areEqual(bind1, bind2)
      case (ErasableLambda(tp1, bind1), ErasableLambda(tp2, bind2)) => areEqual(tp1, tp2) && areEqual(bind1, bind2)
      case (Fix(_, bind1), Fix(_, bind2)) => areEqual(bind1, bind2)
      case (LetIn(_, v1, bind1), LetIn(_, v2, bind2)) => areEqual(v1, v2) && areEqual(bind1, bind2)
      case (MacroTypeDecl(tpe1, bind1), MacroTypeDecl(tpe2, bind2)) => areEqual(tpe1, tpe2) && areEqual(bind1, bind2)
      case (MacroTypeInst(v1, args1), MacroTypeInst(v2, args2)) =>
        if (areEqual(v1, v2) && args1.size == args2.size)
          args1.zip(args2).forall { case (p1, p2) =>
            p1._1 == p2._1 &&
            areEqual(p1._2, p2._2)
          }
        else
          false
      case (NatMatch(n1, t1, bind1), NatMatch(n2, t2, bind2)) => areEqual(n1, n2) && areEqual(t1, t2) && areEqual(bind1, bind2)
      case (EitherMatch(t1, bind11, bind12), EitherMatch(t2, bind21, bind22)) =>
        areEqual(t1, t2) && areEqual(bind11, bind21) && areEqual(bind12, bind22)
      case (Primitive(op1, args1), Primitive(op2, args2)) =>
        if (op1 == op2 && args1.size == args2.size) args1.zip(args2).forall { case (t1, t2) => areEqual(t1, t2)}
        else false
      case (ErasableApp(t11, t12), ErasableApp(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (Fold(tp1, t1), Fold(tp2, t2)) => areEqual(tp1, tp2) && areEqual(t1, t2)
      case (Unfold(t1, bind1), Unfold(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (UnfoldPositive(t1, bind1), UnfoldPositive(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (Abs(bind1), Abs(bind2)) => areEqual(bind1, bind2)
      case (TypeApp(abs1, t1), TypeApp(abs2, t2)) => areEqual(abs1, abs2) && areEqual(t1, t2)
      case (SumType(t1, bind1), SumType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PiType(t1, bind1), PiType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (SigmaType(t1, bind1), SigmaType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (IntersectionType(t1, bind1), IntersectionType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (ExistsType(t1, bind1), ExistsType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RefinementType(t1, bind1), RefinementType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RefinementByType(t1, bind1), RefinementByType(t2, bind2)) =>
        if (solver eq null)
          areEqual(t1, t2) && areEqual(bind1, bind2)
        else
          areEqual(bind1, bind2)
      case (EqualityType(t11, t12), EqualityType(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
      case (RecType(t1, bind1), RecType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => areEqual(bind1, bind2)
      case (Node(name1, args1), Node(name2, args2)) => name1 == name2 && args1.zip(args2).forall { case (arg1, arg2) => areEqual(arg1, arg2) }
      case (Var(x), _) if Solver.targets(x) => solver.recordSolution(x, t2); true
      case (_, Var(x)) if Solver.targets(x) => solver.recordSolution(x, t1); true
      case _ => t1 == t2
    }
  }

  def linearVarsOf(t: Tree): Set[Identifier] = {
    def merge(ids1: Set[Identifier], ids2: Set[Identifier]) =
      (ids1 union ids2) diff (ids1 intersect ids2)
    def rec(t: Tree): Set[Identifier] =
      t match {
        case Var(id) => Set(id)
        case IfThenElse(cond, t1, t2) => merge(merge(rec(cond), rec(t1)), rec(t2))
        case App(t1, t2) => merge(rec(t1), rec(t2))
        case Pair(t1, t2) => merge(rec(t1), rec(t2))
        case Size(t) => rec(t)
        case First(t) => rec(t)
        case Second(t) => rec(t)
        case LeftTree(t) => rec(t)
        case RightTree(t) => rec(t)
        case Bind(id, t) => rec(t) - id
        case Lambda(tp, bind) => merge(tp.toSet.flatMap(rec), rec(bind))
        case Fix(tp, Bind(_, bind)) => merge(tp.toSet.flatMap(rec), rec(bind))
        case LetIn(tp, v, bind) => merge(merge(tp.toSet.flatMap(rec), rec(v)), rec(bind))
        case MacroTypeDecl(tp, bind) => ???
        case MacroTypeInst(v, args) => ???
        case NatMatch(t, t0, bind) => merge(merge(rec(t), rec(t0)), rec(bind))
        case EitherMatch(t, bind1, bind2) => merge(merge(rec(t), rec(bind1)), rec(bind2))
        case Primitive(op, args) => args.map(rec).foldLeft(Set.empty[Identifier])(merge)
        case Fold(tp, t) => merge(rec(tp), rec(t))
        case Unfold(t, bind) => merge(rec(t), rec(bind))
        case UnfoldPositive(t, bind) => merge(rec(t), rec(bind))
        case Abs(bind) => rec(bind)
        case ErasableApp(t1, t2) => merge(rec(t1), rec(t2))
        case TypeApp(abs, tp) => merge(rec(abs), rec(tp))

        case SumType(t1, t2) => merge(rec(t1), rec(t2))
        case PiType(t1, bind) => merge(rec(t1), rec(bind))
        case SigmaType(t1, bind) => merge(rec(t1), rec(bind))
        case IntersectionType(t1, bind) => merge(rec(t1), rec(bind))
        case ExistsType(t1, bind) => merge(rec(t1), rec(bind))
        case RefinementType(t1, bind) => merge(rec(t1), rec(bind))
        case RefinementByType(t1, bind) => merge(rec(t1), rec(bind))
        case RecType(n, bind) => merge(rec(n), rec(bind))
        case PolyForallType(bind) => rec(bind)
        case Node(name, args) => args.map(rec).foldLeft(Set.empty[Identifier])(merge)
        case EqualityType(t1, t2) => merge(rec(t1), rec(t2))

        case BottomType => Set.empty
        case TopType => Set.empty
        case UnitType => Set.empty
        case BoolType => Set.empty
        case NatType => Set.empty
        case UnitLiteral => Set.empty
        case NatLiteral(_) => Set.empty
      }
    rec(t)
  }
}

case class Identifier(id: Int, name: String) extends Positioned {
  override def toString: String = name + "#" + id
  // override def toString: String = name

  def asString(implicit rc: RunContext): String = Printer.asString(this)

  def isTypeIdentifier: Boolean = name.size > 0 && name(0).isUpper
  def isTermIdentifier: Boolean = name.size > 0 && name(0).isLower

  def freshen(): Identifier = Identifier.fresh(name)

  def wrap: String = {
    if (isTypeIdentifier) s"[$this]"
    else s"($this)"
  }

  def isFreeIn(e: Tree): Boolean = {
    e match {
      case Var(id2) => id2 == this
      case IfThenElse(cond, t1, t2) =>
        isFreeIn(t1) || isFreeIn(t2) ||
        isFreeIn(cond)
      case App(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case Pair(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case Size(t) => isFreeIn(t)
      case First(t) => isFreeIn(t)
      case Second(t) => isFreeIn(t)
      case LeftTree(t) => isFreeIn(t)
      case RightTree(t) => isFreeIn(t)
      case Bind(y, e) if (this == y) => false
      case Bind(_, t) => isFreeIn(t)
      case Lambda(tp, bind) => isFreeIn(bind) || tp.exists(isFreeIn)
      case Fix(tp, Bind(n, bind)) => isFreeIn(bind) || tp.exists(isFreeIn)
      case LetIn(tp, v, bind) => isFreeIn(bind) || isFreeIn(v) || tp.exists(isFreeIn)
      case MacroTypeDecl(tp, bind) => isFreeIn(bind) || isFreeIn(tp)
      case MacroTypeInst(v, args) => isFreeIn(v) || args.exists(p => isFreeIn(p._2))
      case NatMatch(t, t0, bind) =>
        isFreeIn(t) || isFreeIn(t0) || isFreeIn(bind)
      case EitherMatch(t, bind1, bind2) =>
        isFreeIn(bind1) || isFreeIn(bind2) ||
        isFreeIn(t)
      case Primitive(op, args) =>
        args.exists(isFreeIn(_))
      case Fold(tp, t) => isFreeIn(t) || isFreeIn(tp)
      case Unfold(t, bind) => isFreeIn(t) || isFreeIn(bind)
      case UnfoldPositive(t, bind) => isFreeIn(t) || isFreeIn(bind)
      case Abs(bind) => isFreeIn(bind)
      case ErasableApp(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case TypeApp(abs, tp) => isFreeIn(abs) && isFreeIn(tp)
      case Error(_, t) => t.map(isFreeIn).getOrElse(false)
      case DefFunction(args, optRet, optMeasure, body, rest) =>
        args.foldLeft((false, false))({
          case ((isFreeAcc, isBoundAcc), arg) =>
            if (isFreeAcc) (isFreeAcc, isBoundAcc)
            else (
              isFreeAcc || (!isBoundAcc && arg.tpe.exists(isFreeIn)),
              isBoundAcc || this == arg.id
            )
        })._1 || optRet.exists(isFreeIn) || optMeasure.exists(isFreeIn) || isFreeIn(body) || isFreeIn(rest)
      case ErasableLambda(ty, bind) => isFreeIn(ty) || isFreeIn(bind)

      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case ExistsType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementByType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RecType(n, bind) => isFreeIn(n) || isFreeIn(bind)
      case PolyForallType(bind) => isFreeIn(bind)
      case Node(name, args) => args.exists(isFreeIn)
      case EqualityType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)

      case BottomType => false
      case TopType => false
      case UnitType => false
      case BoolType => false
      case NatType => false
      case UnitLiteral => false
      case NatLiteral(_) => false
      case BooleanLiteral(_) => false
    }
  }
}

object Identifier {
  var id = 0

  def fresh(): Int = {
    id = id + 1
    id
  }

  def fresh(name: String): Identifier = {
    Identifier(fresh(), name)
  }
}

sealed abstract class Tree extends Positioned {
  def asString(implicit rc: RunContext): String = Printer.asString(this)

  def isBind: Boolean = Tree.isBind(this)

  def isError: Boolean = Tree.isError(this)

  def isValue: Boolean = Tree.isValue(this)

  def isEqual(t: Tree)(implicit rc: RunContext): Boolean = Tree.areEqual(this, t)

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Tree = Tree.replace(id, t, this)

  def traversePost(f: Tree => Unit): Unit = Tree.traverse(this, _ => (), f)
  def traversePre(f: Tree => Unit): Unit = Tree.traverse(this, f, _ => ())
  def traverse(pre: Tree => Unit, post: Tree => Unit): Unit = Tree.traverse(this, pre, post)

  def replace(p: Tree => Option[Either[String,Tree]], post: Tree => Unit)(implicit rc: RunContext): Either[String,Tree] = Tree.replace(p, this, post)
  def replace(p: Tree => Option[Either[String,Tree]])(implicit rc: RunContext): Either[String,Tree] = replace(p, _ => ())

  def preMap(p: Tree => Option[Tree])(implicit rc: RunContext): Tree = Tree.preMap(p, this)

  def postMap(p: Tree => Tree => Tree): Tree = Tree.postMap(p, this)

  def replace(id: Identifier, id2: Identifier)(implicit rc: RunContext): Tree = replace(id, Var(id2))

  def erase()(implicit rc: RunContext): Tree = extraction.Erasure.erase(this)
}

case class Var(id: Identifier) extends Tree {
  setPos(id)
}

case class NatLiteral(n: BigInt) extends Tree {
  require(n >= 0)
}

sealed abstract class AppArgument
case class TypeAppArg(ty: Tree) extends AppArgument
case class AppArg(t: Tree) extends AppArgument
case class ErasableAppArg(t: Tree) extends AppArgument

sealed abstract class DefArgument {
  val id: Identifier
  def toAppArgument(): AppArgument
  val tpe: Option[Tree]
}

case class TypeArgument(id: Identifier) extends DefArgument {
  def toAppArgument(): AppArgument = TypeAppArg(Var(id))
  val tpe = None
}

case class ForallArgument(id: Identifier, ty: Tree) extends DefArgument {
  def toAppArgument(): AppArgument = ErasableAppArg(Var(id))
  val tpe = Some(ty)
}

case class UntypedArgument(id: Identifier) extends DefArgument {
  def toAppArgument(): AppArgument = AppArg(Var(id))
  val tpe = None
}

case class TypedArgument(id: Identifier, ty: Tree) extends DefArgument {
  def toAppArgument(): AppArgument = AppArg(Var(id))
  val tpe = Some(ty)
}

case class Succ(t: Tree) extends Tree
case object UnitLiteral extends Tree
case class BooleanLiteral(b: Boolean) extends Tree
case class Bind(id: Identifier, body: Tree) extends Tree
case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree
case class Lambda(tp: Option[Tree], bind: Tree) extends Tree
case class DefFunction(args: Seq[DefArgument], optRet: Option[Tree], optMeasure: Option[Tree], body: Tree, rest: Tree) extends Tree
case class ErasableLambda(ty: Tree, bind: Tree) extends Tree
case class App(t1: Tree, t2: Tree) extends Tree
case class Pair(t1: Tree, t2: Tree) extends Tree
case class Size(t: Tree) extends Tree
case class First(t: Tree) extends Tree
case class Second(t: Tree) extends Tree
case class Fix(tp: Option[Tree], bind: Tree) extends Tree
case class NatMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree
case class LeftTree(t: Tree) extends Tree
case class RightTree(t: Tree) extends Tree
case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree
case class MacroTypeDecl(tp: Tree, body: Tree) extends Tree
case class MacroTypeInst(v: Tree, args: Seq[(Boolean, Tree)]) extends Tree
case class Error(s: String, t: Option[Tree]) extends Tree
case class Primitive(op: Operator, args: List[Tree]) extends Tree
case class ErasableApp(t1: Tree, t2: Tree) extends Tree
case class Refl(t1: Tree, t2: Tree) extends Tree
case class Fold(tp: Tree, t: Tree) extends Tree
case class Unfold(t: Tree, bind: Tree) extends Tree
case class UnfoldPositive(t: Tree, bind: Tree) extends Tree
case class Abs(t: Tree) extends Tree
case class TypeApp(t1: Tree, t2: Tree) extends Tree
case object BottomType extends Tree
case object TopType extends Tree
case object UnitType extends Tree
case object BoolType extends Tree
case object NatType extends Tree
case class SigmaType(t1: Tree, t2: Tree) extends Tree
case class SumType(t1: Tree, t2: Tree) extends Tree
case class PiType(t1: Tree, t2: Tree) extends Tree
case class IntersectionType(t1: Tree, t2: Tree) extends Tree
case class ExistsType(t1: Tree, t2: Tree) extends Tree
case class RefinementType(t1: Tree, t2: Tree) extends Tree
case class RefinementByType(t1: Tree, t2: Tree) extends Tree
case class RecType(n: Tree, bind: Tree) extends Tree
case class PolyForallType(t: Tree) extends Tree
case class UnionType(t1: Tree, t2: Tree) extends Tree
case class EqualityType(t1: Tree, t2: Tree) extends Tree
case class Because(t1: Tree, t2: Tree) extends Tree
case class Node(name: String, children: Seq[Tree]) extends Tree
