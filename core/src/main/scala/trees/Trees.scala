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
  def isBoolToBoolUnOp: Boolean = Operator.isBoolToBoolBinOp(this)
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
      case RefinementType(t1, bind) => RefinementType(replace(id, v, t1), replace(id, v, bind))
      case RefinementByType(t1, bind) => RefinementByType(replace(id, v, t1), replace(id, v, bind))
      case RecType(n, bind) => RecType(replace(id, v, n), replace(id, v, bind))
      case PolyForallType(bind) => PolyForallType(replace(id, v, bind))

      case BottomType => BottomType
      case TopType => TopType

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $body (${body.getClass}).")
    }
  }

  def traverse_post(t: Tree, f: Tree => Unit): Unit = {
    t match {
      case Var(_) => f(t)
      case UnitLiteral => f(t)
      case NatLiteral(_) => f(t)
      case BooleanLiteral(_) => f(t)
      case IfThenElse(cond, t1, t2) =>
        traverse_post(cond, f)
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case App(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case Pair(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case Size(t) => traverse_post(t, f); f(t)
      case First(t) => traverse_post(t, f); f(t)
      case Second(t) => traverse_post(t, f); f(t)
      case LeftTree(t) => traverse_post(t, f); f(t)
      case RightTree(t) => traverse_post(t, f); f(t)
      case Because(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case Bind(id2, e) =>
        traverse_post(e, f)
        // We don't feed Bind to `f` as it is not a tree on its own
      case Lambda(optTy, bind) =>
        optTy.foreach(ty => traverse_post(ty, f))
        traverse_post(bind, f)
        f(t)
      case ErasableLambda(ty, bind) =>
        traverse_post(ty, f)
        traverse_post(bind, f)
        f(t)
      case Fix(optTy, bind) =>
        optTy.foreach(ty => traverse_post(ty, f))
        traverse_post(bind, f)
        f(t)
      case LetIn(optTy, t, bind) =>
        optTy.foreach(ty => traverse_post(ty, f))
        traverse_post(t, f)
        traverse_post(bind, f)
        f(t)
      case MacroTypeDecl(ty, bind) =>
        traverse_post(ty, f)
        traverse_post(bind, f)
        f(t)
      case MacroTypeInst(v, args) =>
        traverse_post(v, f)
        args.foreach(arg => traverse_post(arg._2, f))
        f(t)
      case NatMatch(t, t0, bind) =>
        traverse_post(t, f)
        traverse_post(t0, f)
        traverse_post(bind, f)
        f(t)
      case EitherMatch(t, bind1, bind2) =>
        traverse_post(t, f)
        traverse_post(bind1, f)
        traverse_post(bind2, f)
        f(t)
      case Primitive(op, args) =>
        args.foreach(arg => traverse_post(arg, f))
        f(t)
      case ErasableApp(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case Fold(tp, t) =>
        traverse_post(tp, f)
        traverse_post(t, f)
        f(t)
      case Unfold(t, bind) =>
        traverse_post(t, f)
        traverse_post(bind, f)
        f(t)
      case UnfoldPositive(t, bind) =>
        traverse_post(t, f)
        traverse_post(bind, f)
        f(t)
      case Abs(bind) =>
        traverse_post(bind, f)
        f(t)
      case TypeApp(abs, t) =>
        traverse_post(abs, f)
        traverse_post(t, f)
        f(t)
      case Error(_, optTy) =>
        optTy.foreach(ty => traverse_post(ty, f))
        f(t)

      case NatType => f(t)
      case BoolType => f(t)
      case UnitType => f(t)
      case SumType(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)
      case PiType(t1, bind) =>
        traverse_post(t1, f)
        traverse_post(bind, f)
        f(t)
      case SigmaType(t1, bind) =>
        traverse_post(t1, f)
        traverse_post(bind, f)
        f(t)
      case IntersectionType(t1, bind) =>
        traverse_post(t1, f)
        traverse_post(bind, f)
        f(t)
      case RefinementType(t1, bind) =>
        traverse_post(t1, f)
        traverse_post(bind, f)
        f(t)
      case RefinementByType(t1, bind) =>
        traverse_post(t1, f)
        traverse_post(bind, f)
        f(t)
      case RecType(n, bind) =>
        traverse_post(n, f)
        traverse_post(bind, f)
        f(t)
      case PolyForallType(bind) =>
        traverse_post(bind, f)
        f(t)
      case EqualityType(t1, t2) =>
        traverse_post(t1, f)
        traverse_post(t2, f)
        f(t)

      case BottomType =>
        f(t)
      case TopType =>
        f(t)

      case _ => throw new java.lang.Exception(s"Function `traverse_post` is not implemented on $t (${t.getClass}).")
    }
  }

  def replace(p: Tree => Option[Either[String,Tree]], body: Tree): Either[String, Tree] = {
    p(body).getOrElse(body match {
      case Var(_) => Right(body)
      case UnitLiteral => Right(body)
      case NatLiteral(_) => Right(body)
      case BooleanLiteral(_) => Right(body)
      case IfThenElse(cond, t1, t2) =>
        for (
          rcond <- replace(p,cond);
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
        IfThenElse(rcond, rt1, rt2)

      case App(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          App(rt1, rt2)

      case Pair(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          Pair(rt1, rt2)

      case Size(t) => replace(p, t).map(Size(_))
      case First(t) => replace(p, t).map(First(_))
      case Second(t) => replace(p, t).map(Second(_))
      case LeftTree(t) => replace(p, t).map(LeftTree(_))
      case RightTree(t) => replace(p, t).map(RightTree(_))
      case Because(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          Because(rt1, rt2)

      case Bind(id, t) => replace(p, t).map(Bind(id, _))
      case Lambda(None, bind) => replace(p, bind).map(Lambda(None, _))
      case Lambda(Some(tp), bind) =>
        for (
          rtp <- replace(p, tp);
          rbind <- replace(p, bind)
        ) yield
          Lambda(Some(rtp), rbind)

      case ErasableLambda(tp, bind) =>
        for (
          rtp <- replace(p, tp);
          rbind <- replace(p, bind)
        ) yield
          ErasableLambda(rtp, rbind)

      case Fix(None, bind) => replace(p, bind).map(Fix(None, _))
      case Fix(Some(tp), bind) =>
        for (
          rtp <- replace(p, tp);
          rbind <- replace(p, bind)
        ) yield
          Fix(Some(rtp), rbind)

      case LetIn(None, v1, bind) =>
        for (
          rv1 <- replace(p, v1);
          rbind <- replace(p, bind)
        ) yield
          LetIn(None, rv1, rbind)
      case LetIn(Some(tp), v1, bind) =>
        for (
          rtp <- replace(p, tp);
          rv1 <- replace(p, v1);
          rbind <- replace(p, bind)
        ) yield
          LetIn(Some(rtp), rv1, rbind)
      case MacroTypeDecl(tp, bind) =>
        for (
          rtp <- replace(p, tp);
          rbind <- replace(p, bind)
        ) yield
          MacroTypeDecl(rtp, rbind)
      case MacroTypeInst(v1, args) =>
        for(
          rv1 <- replace(p, v1);
          eithers = args.map(arg => replace(p, arg._2));
          rargs <- eithers.foldLeft(Right(Seq()): Either[String, Seq[Tree]]) {
            case (acc @ Left(_), _) => acc
            case (_, Left(error)) => Left(error)
            case (Right(acc), Right(rarg)) => Right(acc :+ rarg)
          }
        ) yield
          MacroTypeInst(rv1, args.map(_._1).zip(rargs))

      case NatMatch(t, t0, bind) =>
        for (
          rt <- replace(p, t);
          rt0 <- replace(p, t0);
          rbind <- replace(p, bind)
        ) yield
          NatMatch(rt, rt0, rbind)
      case EitherMatch(t, bind1, bind2) =>
        for (
          rt <- replace(p, t);
          rbind1 <- replace(p, bind1);
          rbind2 <- replace(p, bind2)
        ) yield
          EitherMatch(rt, rbind1, rbind2)
      case Primitive(op, args) =>
        val eithers = args.map(arg => replace(p, arg));
        for(
          rargs <- eithers.foldLeft(Right(Nil): Either[String, List[Tree]]) {
            case (acc @ Left(_), _) => acc
            case (_, Left(error)) => Left(error)
            case (Right(acc), Right(rarg)) => Right(acc :+ rarg)
          }
        ) yield
          Primitive(op, rargs)
      case ErasableApp(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          ErasableApp(rt1, rt2)

      case Fold(tp, t) =>
        for (
          rtp <- replace(p, tp);
          rt <- replace(p, t)
        ) yield
          Fold(rtp, rt)
      case Unfold(t, bind) =>
        for (
          rt <- replace(p,t);
          rbind <- replace(p,bind)
        ) yield
          Unfold(rt, rbind)
      case UnfoldPositive(t, bind) =>
        for (
          rt <- replace(p,t);
          rbind <- replace(p,bind)
        ) yield
          UnfoldPositive(rt, rbind)

      case Abs(bind) => replace(p, bind).map(Abs(_))
      case TypeApp(abs, t) =>
        for (
          rabs <- replace(p,abs);
          rt <- replace(p,t)
        ) yield
          TypeApp(rabs, rt)

      case Error(_, _) => Right(body)

      case NatType => Right(body)
      case BoolType => Right(body)
      case UnitType => Right(body)
      case SumType(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          SumType(rt1, rt2)
      case PiType(t1, bind) =>
        for (
          rt1 <- replace(p,t1);
          rbind <- replace(p,bind)
        ) yield
          PiType(rt1, rbind)
      case SigmaType(t1, bind) =>
        for (
          rt1 <- replace(p,t1);
          rbind <- replace(p,bind)
        ) yield
          SigmaType(rt1, rbind)
      case IntersectionType(t1, bind) =>
        for (
          rt1 <- replace(p,t1);
          rbind <- replace(p,bind)
        ) yield
          IntersectionType(rt1, rbind)
      case RefinementType(t1, bind) =>
        for (
          rt1 <- replace(p,t1);
          rbind <- replace(p,bind)
        ) yield
          RefinementType(rt1, rbind)
      case RefinementByType(t1, bind) =>
        for (
          rt1 <- replace(p,t1);
          rbind <- replace(p,bind)
        ) yield
          RefinementByType(rt1, rbind)
      case RecType(n, bind) =>
        for (
          rn <- replace(p,n);
          rbind <- replace(p,bind)
        ) yield
          RecType(rn, rbind)
      case PolyForallType(bind) =>
        replace(p, bind).map(PolyForallType(_))

      case BottomType => Right(body)
      case TopType => Right(body)

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $body (${body.getClass}).")
    })
  }

  def replaceMany(p: Tree => Option[Tree], body: Tree): Tree = p(body) match {
    case Some(e) => replaceMany(p, e)
    case None => body match {
      case Var(_) => body
      case UnitLiteral => body
      case NatLiteral(_) => body
      case BooleanLiteral(_) => body
      case IfThenElse(cond, t1, t2) =>
        IfThenElse(replaceMany(p, cond), replaceMany(p, t1), replaceMany(p, t2))
      case App(t1, t2) =>
        App(replaceMany(p, t1), replaceMany(p, t2))
      case Pair(t1, t2) => Pair(replaceMany(p, t1), replaceMany(p, t2))
      case Size(t) => Size(replaceMany(p, t))
      case First(t) => First(replaceMany(p, t))
      case Second(t) => Second(replaceMany(p, t))
      case LeftTree(t) => LeftTree(replaceMany(p, t))
      case RightTree(t) => RightTree(replaceMany(p, t))
      case Because(t1, t2) => Because(replaceMany(p, t1), replaceMany(p, t2))
      case Bind(id2, e) => Bind(id2, replaceMany(p, e))
      case Lambda(None, bind) => Lambda(None, replaceMany(p, bind))
      case Lambda(Some(tp), bind) => Lambda(Some(replaceMany(p, tp)), replaceMany(p, bind))
      case ErasableLambda(tp, bind) => ErasableLambda(replaceMany(p, tp), replaceMany(p, bind))
      case Fix(None, bind) => Fix(None, replaceMany(p, bind))
      case Fix(Some(tp), bind) => Fix(Some(replaceMany(p, tp)), replaceMany(p, bind))
      case LetIn(None, v1, bind) => LetIn(None, replaceMany(p, v1), replaceMany(p, bind))
      case LetIn(Some(tp), v1, bind) => LetIn(Some(replaceMany(p, tp)), replaceMany(p, v1), replaceMany(p, bind))
      case MacroTypeDecl(tpe, bind) => MacroTypeDecl(replaceMany(p, tpe), replaceMany(p, bind))
      case MacroTypeInst(v1, args) =>
        MacroTypeInst(
          replaceMany(p, v1),
          args.map(a => (a._1, replaceMany(p, a._2)))
        )
      case NatMatch(t, t0, bind) => NatMatch(replaceMany(p, t), replaceMany(p, t0), replaceMany(p, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replaceMany(p, t), replaceMany(p, bind1), replaceMany(p, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replaceMany(p, _)))
      case ErasableApp(t1, t2) => ErasableApp(replaceMany(p, t1), replaceMany(p, t2))
      case Fold(tp, t) => Fold(replaceMany(p, tp), replaceMany(p, t))
      case Unfold(t, bind) => Unfold(replaceMany(p, t), replaceMany(p, bind))
      case UnfoldPositive(t, bind) => UnfoldPositive(replaceMany(p, t), replaceMany(p, bind))
      case Abs(bind) => Abs(replaceMany(p, bind))
      case TypeApp(abs, t) => TypeApp(replaceMany(p, abs), replaceMany(p, t))
      case Error(_, _) => body

      case NatType => body
      case BoolType => body
      case UnitType => body
      case SumType(t1, t2) => SumType(replaceMany(p, t1), replaceMany(p, t2))
      case PiType(t1, bind) => PiType(replaceMany(p, t1), replaceMany(p, bind))
      case SigmaType(t1, bind) => SigmaType(replaceMany(p, t1), replaceMany(p, bind))
      case IntersectionType(t1, bind) => IntersectionType(replaceMany(p, t1), replaceMany(p, bind))
      case RefinementType(t1, bind) => RefinementType(replaceMany(p, t1), replaceMany(p, bind))
      case RefinementByType(t1, bind) => RefinementByType(replaceMany(p, t1), replaceMany(p, bind))
      case RecType(n, bind) => RecType(replaceMany(p, n), replaceMany(p, bind))
      case PolyForallType(bind) => PolyForallType(replaceMany(p, bind))

      case BottomType => BottomType
      case TopType => TopType

      case _ => throw new java.lang.Exception(s"Function `replaceMany` is not implemented on $body (${body.getClass}).")
    }
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

  def areEqual(t1: Tree, t2: Tree)(implicit rc: RunContext): Boolean = {
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
      case (RefinementType(t1, bind1), RefinementType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RefinementByType(t1, bind1), RefinementByType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (RecType(t1, bind1), RecType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => areEqual(bind1, bind2)
      case _ => t1 == t2
    }
  }
}

case class Identifier(id: Int, name: String) extends Positioned {
  override def toString: String = name + "#" + id
  // override def toString: String = name

  def isTypeIdentifier: Boolean = name.size > 0 && name(0).isUpper
  def isTermIdentifier: Boolean = name.size > 0 && name(0).isLower

  def wrap: String = {
    if (isTypeIdentifier) s"[$this]"
    else s"($this)"
  }

  def isFreeIn(e: Tree): Boolean = {
    e match {
      case Var(id2) if id2 == this => true
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
      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementByType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RecType(n, bind) => isFreeIn(n) || isFreeIn(bind)
      case PolyForallType(bind) => isFreeIn(bind)
      case _ => false
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
  def isBind: Boolean = Tree.isBind(this)

  def isError: Boolean = Tree.isError(this)

  def isValue: Boolean = Tree.isValue(this)

  def isEqual(t: Tree)(implicit rc: RunContext): Boolean = Tree.areEqual(this, t)

  def replace(id: Identifier, t: Tree)(implicit rc: RunContext): Tree = Tree.replace(id, t, this)

  def traverse_post(f: Tree => Unit): Unit = Tree.traverse_post(this, f)

  def replace(p: Tree => Option[Either[String,Tree]]): Either[String,Tree] = Tree.replace(p, this)

  def replaceMany(p: Tree => Option[Tree]): Tree = Tree.replaceMany(p, this)

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
}

case class TypeArgument(id: Identifier) extends DefArgument {
  def toAppArgument(): AppArgument = TypeAppArg(Var(id))
}

case class ForallArgument(id: Identifier, ty: Tree) extends DefArgument {
  def toAppArgument(): AppArgument = ErasableAppArg(Var(id))
}

case class UntypedArgument(id: Identifier) extends DefArgument {
  def toAppArgument(): AppArgument = AppArg(Var(id))
}

case class TypedArgument(id: Identifier, ty: Tree) extends DefArgument {
  def toAppArgument(): AppArgument = AppArg(Var(id))
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
case class RefinementType(t1: Tree, t2: Tree) extends Tree
case class RefinementByType(t1: Tree, t2: Tree) extends Tree
case class RecType(n: Tree, bind: Tree) extends Tree
case class PolyForallType(t: Tree) extends Tree
case class UnionType(t1: Tree, t2: Tree) extends Tree
case class EqualityType(t1: Tree, t2: Tree) extends Tree
case class Because(t1: Tree, t2: Tree) extends Tree
