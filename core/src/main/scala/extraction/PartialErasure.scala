package stainlessfit
package core
package extraction

import codegen.CodeGen
import parser.FitParser
import trees._
import util.RunContext

class PartialErasure(implicit val rc: RunContext) extends Phase[Unit] {
  def transform(t: Tree): (Tree, Unit) = (PartialErasure.erase(t, true), ())
}

object PartialErasure {
  def erase(t: Tree, topLevel: Boolean = false)(implicit rc: RunContext): Tree = t match {
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
    case Because(t1, t2) => erase(t1)
    case Bind(id2, e) => Bind(id2, erase(e, topLevel))
    case Lambda(tpe, bind) => Lambda(tpe, erase(bind))
    case ErasableLambda(_, Bind(id, body)) => erase(body)

    case Fix(tpe, bind) => bind match {
      case TreeBuilders.Binds(_, tree) => erase(tree)
    }

    case LetIn(tpe, t1, bind) => LetIn(tpe, erase(t1), erase(bind)) //App(Lambda(None, erase(bind)), erase(t1))  //Let(None, erase(t1), erase(bind))
    case MacroTypeDecl(tpe, Bind(id, body)) => erase(body)
    case NatMatch(t, t0, bind) => NatMatch(erase(t), erase(t0), erase(bind))

    // case NatMatch(t, t0, bind) => {
    //   val cond = Primitive(Eq, List(t, NatLiteral(BigInt(0))))
    //   erase(IfThenElse(cond, t0, bind))
    // }

    case EitherMatch(t, bind1, bind2) => EitherMatch(erase(t), erase(bind1), erase(bind2))
    case Primitive(op, args) => Primitive(op, args.map(erase(_)))
    case ErasableApp(t1, _) => erase(t1)
    case Fold(_, t) => erase(t)
    case Unfold(t1, bind) => erase(LetIn(None, t1, bind))
    case UnfoldPositive(t1, bind) => erase(LetIn(None, t1, bind))
    case Abs(Bind(id, body)) => erase(body)
    case TypeApp(t1, _) => erase(t1)
    case Error(s, _) => Error(s, None)

    case defFun @ DefFunction(_, _, _, _, _) if !topLevel => {
      eraseDefFun(defFun)
    }


    case defFun @ DefFunction(args, optReturnType, optMeasure, body, rest) => {
      DefFunction(args, optReturnType, optMeasure, erase(body, false), erase(rest, true))
    }

    case _ => rc.reporter.fatalError(s"Partial Erasure is not implemented on $t (${t.getClass}).")
  }

  def eraseDefFun(defFun: DefFunction)(implicit rc: RunContext) = {

    val DefFunction(args, optReturnType, optMeasure, bind, rest) = defFun
    val (ids, body) = bind match {
      case TreeBuilders.Binds(ids, body) => (ids, body)
    }

    //TODO Might not need to know the return type
    // val retType = optReturnType.getOrElse(rc.reporter.fatalError(s"Need a declared return type to codegen function $defFun"))
    // val (valueType, value) = if(args.isEmpty) {
    //   (retType, body)
    // } else {
    //   val TypedArgument(arg, argType) = args.head
    //   (PiType(argType, retType), Lambda(Some(argType), Bind(ids.head, body)))
    // }
    //
    // erase(LetIn(Some(valueType), value, rest))

    val value = if(args.isEmpty) {
      body
    } else {
      val TypedArgument(arg, argType) = args.head
      Lambda(Some(argType), Bind(ids.head, body))
    }

    erase(LetIn(None, value, rest))
  }
}
