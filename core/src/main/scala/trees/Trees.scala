package core
package trees


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
case object Lteq extends Operator {
  override def toString = "<="
}
case object Gteq extends Operator {
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
      case Lteq => true
      case Gteq => true
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
    case "<=" => Some(Lteq)
    case ">=" => Some(Gteq)
    case "<" => Some(Lt)
    case ">" => Some(Gt)
    case _ => None
  }
}

object Tree {
  def setId(t: Tree, m: Map[Identifier, Identifier], max: Int): (Tree, Int) = {
    t match {
      case UnitLiteral => (t, max)
      case NatLiteral(_) => (t, max)
      case BooleanLiteral(_) => (t, max)
      case UnitType => (t, max)
      case NatType => (t, max)
      case BoolType => (t, max)
      case Error(s, Some(t)) =>
        val (newT, max1) = setId(t, m, max)
        (Error(s, Some(newT)), max1)
      case Error(_, None) => (t, max)
      case Var(id) =>
        m.get(id) match {
          case None => throw new java.lang.Exception(s"Error in name resolution: undefined variable $id at position ${t.pos}")
          case Some(newId) => (Var(newId), max)
        }
      case IfThenElse(cond, t1, t2) =>
        val (newC, max1) = setId(cond, m, max)
        val (newT1, max2) = setId(t1, m, max1)
        val (newT2, max3) = setId(t2, m, max2)
        (IfThenElse(newC, newT1, newT2), max3)
      case App(t1, t2) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newT2, max2) = setId(t2, m, max1)
        (App(newT1, newT2), max2)
      case Pair(t1, t2) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newT2, max2) = setId(t2, m, max1)
        (Pair(newT1, newT2), max2)
      case Size(t) =>
        val (newT, max1) = setId(t, m, max)
        (Size(newT), max1)
      case First(t) =>
        val (newT, max1) = setId(t, m, max)
        (First(newT), max1)
      case Second(t) =>
        val (newT, max1) = setId(t, m, max)
        (Second(newT), max1)
      case LeftTree(t) =>
        val (newT, max1) = setId(t, m, max)
        (LeftTree(newT), max1)
      case RightTree(t) =>
        val (newT, max1) = setId(t, m, max)
        (RightTree(newT), max1)
      case Bind(y, e) =>
        val m1 = m.updated(y, Identifier(max, y.name))
        val (newE, max2) = setId(e, m1, max + 1)
        (Bind(Identifier(max, y.name), newE), max2)
      case Lambda(Some(tp), bind) =>
        val (newTp, max1) = setId(tp, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (Lambda(Some(newTp), newBind), max2)
      case Lambda(None, bind) =>
        val (newBind, max1) = setId(bind, m, max)
        (Lambda(None, newBind), max1)
      case ErasableLambda(tp, bind) =>
        val (newTp, max1) = setId(tp, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (ErasableLambda(newTp, newBind), max2)
      case Fix(Some(tp), bind) =>
        val (newTp, max1) = setId(tp, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (Fix(Some(newTp), newBind), max2)
      case Fix(None, bind) =>
        val (newBind, max1) = setId(bind, m, max)
        (Fix(None, newBind), max1)

      case LetIn(Some(tp), v, bind) =>
        val (newTp, max1) = setId(tp, m, max)
        val (newV, max2) = setId(v, m, max1)
        val (newBind, max3) = setId(bind, m, max2)
        (LetIn(Some(newTp), newV, newBind), max3)
      case LetIn(None, v, bind) =>
        val (newV, max1) = setId(v, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (LetIn(None, newV, newBind), max2)
      case MacroTypeDecl(tpe, bind) =>
        val (newTpe, max1) = setId(tpe, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (MacroTypeDecl(newTpe, newBind), max2)
      case MacroTypeInst(v, args) =>
        val (newV, max1) = setId(v, m, max)
        val newArgs =
          args.scanLeft((true, (UnitLiteral: Tree, max1))) {
            case (cmax, (isTerm, arg)) =>
              (isTerm, setId(arg, m, cmax._2._2))
          }.tail
        (MacroTypeInst(newV.asInstanceOf[Var], newArgs.map(p => (p._1, p._2._1))), newArgs.last._2._2)

      case Match(t, t0, bind) =>
        val (newT, max1) = setId(t, m, max)
        val (newT0, max2) = setId(t0, m, max1)
        val (newBind, max3) = setId(bind, m, max2)
        (Match(newT, newT0, newBind), max3)
      case EitherMatch(t, bind1, bind2) =>
        val (newT, max1) = setId(t, m, max)
        val (newBind1, max2) = setId(bind1, m, max1)
        val (newBind2, max3) = setId(bind2, m, max2)
        (EitherMatch(newT, newBind1, newBind2), max3)
      case Primitive(op, t ::  Nil) =>
        val (newT, max1) = setId(t, m, max)
        (Primitive(op, newT ::  Nil), max1)
      case Primitive(op, t1 ::  t2 ::  Nil) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newT2, max2) = setId(t2, m, max1)
        (Primitive(op, newT1 ::  newT2 ::  Nil), max2)
      case Inst(t1, t2) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newT2, max2) = setId(t2, m, max1)
        (Inst(newT1, newT2), max2)
      case Fold(tp, t) =>
        val (newTp, max1) = setId(tp, m, max)
        val (newT, max2) = setId(t, m, max1)
        (Fold(newTp, newT), max2)
      case Unfold(t, bind) =>
        val (newT,max1) = setId(t, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (Unfold(newT, newBind), max2)
      case UnfoldPositive(t, bind) =>
        val (newT,max1) = setId(t, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (UnfoldPositive(newT, newBind), max2)
      case Abs(bind) =>
        val (newBind, max1) = setId(bind, m, max)
        (Abs(newBind), max1)
      case TypeApp(abs, t) =>
        val (newAbs, max1) = setId(abs, m, max)
        val (newT, max2) = setId(t, m, max1)
        (TypeApp(newAbs, newT), max2)
      case SumType(t1, t2) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newT2, max2) = setId(t2, m, max1)
        (SumType(newT1, newT2), max2)
      case PiType(t1, bind) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (PiType(newT1, newBind), max2)
      case SigmaType(t1, bind) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (SigmaType(newT1, newBind), max2)
      case IntersectionType(t1, bind) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (IntersectionType(newT1, newBind), max2)
      case RefinementType(t1, bind) =>
        val (newT1, max1) = setId(t1, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (RefinementType(newT1, newBind), max2)
      case RecType(n, bind) =>
        val (newN, max1) = setId(n, m, max)
        val (newBind, max2) = setId(bind, m, max1)
        (RecType(newN, newBind), max2)
      case PolyForallType(bind) =>
        val (newBind, max1) = setId(bind, m, max)
        (PolyForallType(newBind), max1)

      case _ => throw new java.lang.Exception(s"Function `setId` is not defined on tree: $t")
    }
  }

  def replaceBind(bind: Tree, v: Tree): Tree = {
    require(isBind(bind))
    bind match {
      case Bind(id, body) => replace(id, v, body)
      case t => t
    }
  }

  def replace(id: Identifier, v: Tree, body: Tree): Tree = {
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
        assert(!id2.isFreeIn(v))
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
      case Match(t, t0, bind) => Match(replace(id, v, t), replace(id, v, t0), replace(id, v, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replace(id, v, t), replace(id, v, bind1), replace(id, v, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replace(id, v, _)))
      case Inst(t1, t2) => Inst(replace(id, v, t1), replace(id, v, t2))
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
      case RecType(n, bind) => RecType(replace(id, v, n), replace(id, v, bind))
      case PolyForallType(bind) => PolyForallType(replace(id, v, bind))

      case BottomType => BottomType
      case TopType => TopType

      case _ => throw new java.lang.Exception(s"Function `replace` is not implemented on $body (${body.getClass}).")
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

      case Match(t, t0, bind) =>
        for (
          rt <- replace(p, t);
          rt0 <- replace(p, t0);
          rbind <- replace(p, bind)
        ) yield
          Match(rt, rt0, rbind)
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
      case Inst(t1, t2) =>
        for (
          rt1 <- replace(p,t1);
          rt2 <- replace(p,t2)
        ) yield
          Inst(rt1, rt2)

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
      case Match(t, t0, bind) => Match(replaceMany(p, t), replaceMany(p, t0), replaceMany(p, bind))
      case EitherMatch(t, bind1, bind2) => EitherMatch(replaceMany(p, t), replaceMany(p, bind1), replaceMany(p, bind2))
      case Primitive(op, args) => Primitive(op, args.map(replaceMany(p, _)))
      case Inst(t1, t2) => Inst(replaceMany(p, t1), replaceMany(p, t2))
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
      case RecType(n, bind) => RecType(replaceMany(p, n), replaceMany(p, bind))
      case PolyForallType(bind) => PolyForallType(replaceMany(p, bind))

      case BottomType => BottomType
      case TopType => TopType

      case _ => throw new java.lang.Exception(s"Function `replaceMany` is not implemented on $body (${body.getClass}).")
    }
  }

  def erase(t: Tree): Tree = t match {
    case Var(_) => t
    case UnitLiteral => t
    case NatLiteral(_) => t
    case BooleanLiteral(_) => t
    case Refl(_, _) => UnitLiteral
    case IfThenElse(cond, t1, t2) => IfThenElse(erase(cond), erase(t1), erase(t2))
    case App(t1, t2) => App(erase(t1), erase(t2))
    case Pair(t1, t2) => Pair(erase(t1), erase(t2))
    case Size(t) => Size(erase(t))
    case First(t) => First(erase(t))
    case Second(t) => Second(erase(t))
    case LeftTree(t) => LeftTree(erase(t))
    case RightTree(t) => RightTree(erase(t))
    case Because(t1, t2) => Because(erase(t1), erase(t2))
    case Bind(id2, e) => Bind(id2, erase(e))
    case Lambda(_, bind) => Lambda(None, erase(bind))
    case ErasableLambda(_, Bind(id, body)) => erase(body)
    case Fix(_, bind) => Fix(None, erase(bind))
    case LetIn(_, t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case MacroTypeDecl(tpe, Bind(id, body)) => erase(body)
    case Match(t, t0, bind) => Match(erase(t), erase(t0), erase(bind))
    case EitherMatch(t, bind1, bind2) => EitherMatch(erase(t), erase(bind1), erase(bind2))
    case Primitive(op, args) => Primitive(op, args.map(erase(_)))
    case Inst(t1, _) => erase(t1)
    case Fold(_, t) => erase(t)
    case Unfold(t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case UnfoldPositive(t1, bind) => App(Lambda(None, erase(bind)), erase(t1))
    case Abs(Bind(id, body)) => erase(body)
    case TypeApp(t1, _) => erase(t1)
    case Error(s, _) => Error(s, None)
    case _ => throw new java.lang.Exception(s"Function erase is not implemented on $t (${t.getClass}).")
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
      case Abs(_) => true
      case _ => false
    }
  }

  def isBind(t: Tree): Boolean = t.isInstanceOf[Bind]

  def isObviousSubType(ty1: Tree, ty2: Tree): Boolean = {
    (ty1, ty2) match {
      case (BottomType, _) => true
      case (_, TopType) => true
      case (ty1, ty2) if ty1 == ty2 => true
      case (RefinementType(ty, Bind(a, t)), ty2) => isObviousSubType(ty, ty2)
      case (SumType(l1, r1), SumType(l2, r2)) => isObviousSubType(l1, l2) && isObviousSubType(r1, r2)
      case (SigmaType(l1, Bind(x, r1)), SigmaType(l2, Bind(y, r2))) =>
        isObviousSubType(l1, l2) && isObviousSubType(r1, r2.replace(y, Var(x)))
      case (PiType(ty1, Bind(x, ty1b)), PiType(ty2, Bind(y, ty2b))) =>
        isObviousSubType(ty2, ty1) && isObviousSubType(ty1b, ty2b.replace(y, Var(x)))
      case (IntersectionType(ty1, Bind(x, ty1b)), IntersectionType(ty2, Bind(y, ty2b))) =>
        isObviousSubType(ty2, ty1) && isObviousSubType(ty2b, ty1b.replace(y, Var(x)))
      case (PolyForallType(Bind(x1, ty1)), PolyForallType(Bind(x2, ty2))) =>
        isObviousSubType(ty1, ty2.replace(x2, Var(x1)))
      case _ => false
    }
  }

  def areEqual(t1: Tree, t2: Tree): Boolean = {
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
      case (Match(n1, t1, bind1), Match(n2, t2, bind2)) => areEqual(n1, n2) && areEqual(t1, t2) && areEqual(bind1, bind2)
      case (EitherMatch(t1, bind11, bind12), EitherMatch(t2, bind21, bind22)) =>
        areEqual(t1, t2) && areEqual(bind11, bind21) && areEqual(bind12, bind22)
      case (Primitive(op1, args1), Primitive(op2, args2)) =>
        if (op1 == op2 && args1.size == args2.size) args1.zip(args2).forall { case (t1, t2) => areEqual(t1, t2)}
        else false
      case (Inst(t11, t12), Inst(t21, t22)) => areEqual(t11, t21) && areEqual(t12, t22)
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
      case (RecType(t1, bind1), RecType(t2, bind2)) => areEqual(t1, t2) && areEqual(bind1, bind2)
      case (PolyForallType(bind1), PolyForallType(bind2)) => areEqual(bind1, bind2)
      case _ => t1 == t2
    }
  }
}

case class Identifier(id: Int, name: String) extends Positioned {
  // override def toString: String = name + "#" + id
  override def toString: String = name

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
      case Match(t, t0, bind) =>
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
      case Inst(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case TypeApp(abs, tp) => isFreeIn(abs) && isFreeIn(tp)
      case SumType(t1, t2) => isFreeIn(t1) || isFreeIn(t2)
      case PiType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case SigmaType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case IntersectionType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RefinementType(t1, bind) => isFreeIn(t1) || isFreeIn(bind)
      case RecType(n, bind) => isFreeIn(n) || isFreeIn(bind)
      case PolyForallType(bind) => isFreeIn(bind)
      case _ => false
    }
  }
}

sealed abstract class Tree extends Positioned {
  def isBind: Boolean = Tree.isBind(this)

  def isError: Boolean = Tree.isError(this)

  def isValue: Boolean = Tree.isValue(this)

  def isObviousSubType(ty: Tree): Boolean = Tree.isObviousSubType(this, ty)

  def isEqual(t: Tree): Boolean = Tree.areEqual(this, t)

  def replace(id: Identifier, t: Tree): Tree = Tree.replace(id, t, this)

  def replace(p: Tree => Option[Either[String,Tree]]): Either[String,Tree] = Tree.replace(p, this)

  def replaceMany(p: Tree => Option[Tree]): Tree = Tree.replaceMany(p, this)

  def replace(id: Identifier, id2: Identifier): Tree = replace(id, Var(id2))

  def erase(): Tree = Tree.erase(this)

  def toStringPar: String = {
    val s = toString
    this match {
      case Var(_) => s
      case UnitLiteral => s
      case BooleanLiteral(_) => s
      case NatLiteral(_) => s
      case _ =>
        if (s(0) == '(') s
        else "(" + s + ")"
    }
  }
}

case class Var(id: Identifier) extends Tree {
  setPos(id)
  override def toString: String = id.toString
}

case class NatLiteral(n: BigInt) extends Tree {
  require(n >= 0)
  override def toString: String = n.toString
}

case class Succ(t: Tree) extends Tree

case object UnitLiteral extends Tree {
  override def toString: String = "unit"
}

case class BooleanLiteral(b: Boolean) extends Tree {
   override def toString: String = if (b) "true" else "false"
}

case class Bind(id: Identifier, body: Tree) extends Tree {
   private def bodyString(): String = {
    " => {\n  " + body.toString.replaceAll("\n", "\n  ") + "\n}"
  }

  override def toString: String = id.toString + bodyString()

  def toStringWithType(ty: Tree): String = {
    id.toString + ": " + ty.toString + bodyString()
  }
}

case class IfThenElse(cond: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "if (" + cond.toString + ") {\n" +
    "  " + t1.toString.replaceAll("\n", "\n  ") + "\n" +
    "}" + "\n" +
    "else {" + "\n" +
    "  " + t2.toString.replaceAll("\n", "\n  ") + "\n" +
    "}"
  }
}

case class Lambda(tp: Option[Tree], bind: Tree) extends Tree {
  override def toString: String = {
    (tp, bind) match {
      case (Some(ty), Bind(id, body)) => s"fun ($id: $ty) => {\n  ${body.toString.replaceAll("\n", "\n  ")}\n}"
      case (None, Bind(id, body)) => s"fun $id => {\n  ${body.toString.replaceAll("\n", "\n  ")}\n}"
      case _ => "<Missing bind in λ>"
    }
  }
}

case class ErasableLambda(ty: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(id, body) =>
        s"fun {{$id: $ty}} => {\n  ${body.toString.replaceAll("\n", "\n  ")}\n}"
      case _ => "<Missing bind in ErasableLambda>"
    }
  }
}

case class App(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t1.toString + " " + t2.toStringPar
  }
}

case class Pair(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
     "(" + t1.toString + ", " + t2.toString + ")"
  }
}

case class Size(t: Tree) extends Tree {
  override def toString: String = {
    "Size(" + t.toString + ")"
  }
}

case class First(t: Tree) extends Tree {
  override def toString: String = {
    "First(" + t.toString + ")"
  }
}

case class Second(t: Tree) extends Tree {
  override def toString: String = {
    "Second(" + t.toString + ")"
  }
}

case class Fix(tp: Option[Tree], bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(n1, Bind(x, body)) =>
        val tyString = tp match {
          case Some(Bind(n, ty)) => "[" + n.toString + " => " + ty.toString + "]"
          case _ => ""
        }
        "Fix" + tyString + "(\n" +
        "  " + n1.toString + ", " + Bind(x, body).toString.replaceAll("\n", "\n  ") +
        "\n)"
      case _ => s"<Missing bind in Fix($tp, $bind)>"
    }
  }
}

case class Match(t: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(n, tn) =>
        t.toString + " match {\n" +
        "  case 0 =>\n" +
        t1.toString.replaceAll("\n", "\n    ") + "\n"
        "  case " + n.toString + " =>\n" +
        tn.toString.replaceAll("\n", "\n    ") + "\n}"
      case _ => "<Missing bind in Match>"
    }
  }
}

case class EitherMatch(t: Tree, t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    (t1, t2) match {
      case (Bind(x1, t1), Bind(x2, t2)) =>
        t.toString + " match {\n" +
        "  case Left(" + x1.toString + ") =>\n    " +
        t1.toString.replaceAll("\n", "\n    ") + "\n" +
        "  case Right(" + x2.toString + ") =>\n    " +
        t2.toString.replaceAll("\n", "\n    ") + "\n}"
      case _ => "<Missing bind in EitherMatch>"
    }
  }
}

case class LeftTree(t: Tree) extends Tree {
  override def toString: String = {
    "Left(" + t.toString + ")"
  }
}

case class RightTree(t: Tree) extends Tree {
  override def toString: String = {
    "Right(" + t.toString + ")"
  }
}

case class LetIn(tp: Option[Tree], v: Tree, body: Tree) extends Tree {
  override def toString: String = {
    body match {
      case Bind(x, t) =>
        val typeString = tp match {
            case Some(ty) => ": " + ty.toString
            case _ => ""
          }
        "val " + x.toString + typeString + " = " + v.toString + ";\n" +
        t.toString
      case _ => throw new Exception("Missing bind in LetIn")
    }
  }
}

case class MacroTypeDecl(tp: Tree, body: Tree) extends Tree {
  override def toString: String = {
    body match {
      case Bind(x, t) =>
        def binds(acc: Seq[Identifier], t: Tree): (Seq[Identifier], Tree) = t match {
          case Bind(id, body) => binds(acc :+ id, body)
          case _ => (acc, t)
        }
        val (params, tpe) = binds(Seq(), tp)
        s"[type $x${params.map(_.wrap).mkString} = $tpe]\n$t"
      case _ => throw new Exception("Missing bind in MacroTypeDecl")
    }
  }
}

case class MacroTypeInst(v: Tree, args: Seq[(Boolean, Tree)]) extends Tree {
  require(!args.isEmpty)
  override def toString: String = {
    s"$v${args.map { case (isTerm, arg) =>
      if (isTerm) "(" + arg + ")"
      else "[" + arg + "]"
    }.mkString}"
  }
}

case class Error(s: String, t: Option[Tree]) extends Tree {
  override def toString: String = t match {
    case None => s"Error($s)"
    case Some(tp) => s"Error[$tp]($s)"
  }
}

case class Primitive(op: Operator, args: List[Tree]) extends Tree {
  override def toString: String = {
    args match {
      case n1 ::  Nil => s"$op($n1)"
      case n1 ::  n2 ::  Nil =>
        n1.toStringPar + op.toString + n2.toStringPar
      case _ => throw new java.lang.Exception("Primitive operations have one or two arguments.")
    }
  }
}

case class Inst(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    s"$t1[{$t2}]"
  }
}

case class Refl(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "Refl(" + t1.toString + ", " + t2.toString + ")"
  }
}

case class Fold(tp: Tree, t: Tree) extends Tree {
  override def toString: String = {
    s"[fold as $tp]($t)"
  }
}

case class Unfold(t: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(x, body) => s"[unfold] val $x = $t;\n$body"
      case _ => "<Missing bind in Unfold>"
    }
  }
}

case class UnfoldPositive(t: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(x, body) => s"[unfold positive] val $x = $t;\n$body"
      case _ => "<Missing bind in UnfoldPositive>"
    }
  }
}

case class Abs(t: Tree) extends Tree {
  override def toString: String = {
    t match {
      case Bind(a, t) =>
        "Λ" + a.toString + ". " + t.toString
      case _ => "<Missing bind in Abs>"
    }
  }
}

case class TypeApp(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    s"$t1[$t2]"
  }
}

case object BottomType extends Tree {
  override def toString: String = "⊥"
}

case object TopType extends Tree {
  override def toString: String = "⊤"
}

case object UnitType extends Tree {
  override def toString: String = "Unit"
}

case object BoolType extends Tree {
  override def toString: String = "Bool"
}

case object NatType extends Tree {
  override def toString: String = "Nat"
}

case class SigmaType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(Σ" + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in SigmaType>"
    }
  }
}

case class SumType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    "(" + t1.toString + ") + (" + t2.toString + ")"
  }
}

case class PiType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(Π " + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in PiType>"
    }
  }
}

case class IntersectionType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "(∀" + x.toString + ": " + t1.toString + ". " + t2.toString + ")"
      case _ => "<Missing bind in IntersectionType>"
    }
  }
}

case class RefinementType(t1: Tree, t2: Tree) extends Tree {
  override def toString: String = {
    t2 match {
      case Bind(x, t2) =>
        "{" + x.toString + ": " + t1.toString + " | " + t2.toString + "}"
      case _ => "<Missing bind in RefinementType>"
    }
  }
}

case class RecType(n: Tree, bind: Tree) extends Tree {
  override def toString: String = {
    bind match {
      case Bind(a, ty) =>
        "(Rec(" + n.toString + ")(" + a.toString + " => " + ty.toString + ")"
      case _ => "<Missing bind in RecType>"
    }
  }
}

case class PolyForallType(t: Tree) extends Tree {
  override def toString: String = {
    t match {
      case Bind(a, t) =>
        "(∀" + a.toString + ": Type. " + t.toString
      case _ => "<Missing bind in PolyForallType>"
    }
  }
}

case class UnionType(t1: Tree, t2: Tree) extends Tree

case class EqualityType(t1: Tree, t2: Tree) extends Tree

case class SingletonType(t: Tree) extends Tree

case class Because(t1: Tree, t2: Tree) extends Tree
