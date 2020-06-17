package stainlessfit
package core
package trees

import stainlessfit.core.util.Utils._
import stainlessfit.core.util.RunContext

object TreeUtils{


  /* Traverses the Tree <body>, 
   * replaces the first subtree <t> for which p(t)=Some(newT),
   * By newT
   * Returns Some(the transformed tree) 
   *         or None, if no subtree was matched by p
   */
  def replaceSmallStep(p: Tree => Option[Tree], body: Tree)(implicit rc: RunContext): Option[Tree] = {
    def np[A](t: Tree, discarted: A): Option[Tree] = p(t)
    replaceFirstConditionalOnSuperTree(np,body,(_,_) => false)
    
    /* TODO: Remove v
    def rss(body: Tree) = replaceSmallStep(p, body)
    p(body) match {
      case Some(e) => Some(e)
      case None => body match {
        case Var(_) => None
        case UnitLiteral => None
        case NatLiteral(_) => None
        case BooleanLiteral(_) => None
        case IfThenElse(cond, t1, t2) =>
            rss(cond).map(IfThenElse(_,t1,t2)) orElse
            rss(t1).map(IfThenElse(cond,_,t2)) orElse
            rss(t2).map(IfThenElse(cond,t1,_))
        case App(t1, t2) =>
            rss(t1).map(App(_,t2)) orElse
            rss(t2).map(App(t1,_))
        case Pair(t1, t2) =>
            rss(t1).map(Pair(_,t2)) orElse
            rss(t2).map(Pair(t1,_))
        case Size(t) =>
            rss(t).map(Size(_))
        case First(t) =>
            rss(t).map(First(_))
        case Second(t) =>
            rss(t).map(Second(_))
        case LeftTree(t) =>
            rss(t).map(LeftTree(_))
        case RightTree(t) =>
            rss(t).map(RightTree(_))
        case Because(t1, t2) =>
            rss(t1).map(Because(_,t2)) orElse
            rss(t2).map(Because(t1,_))
        case Bind(id2, t) =>
            rss(t).map(Bind(id2,_))
        case Lambda(op, bind) => 
            op.flatMap(rss(_).map(x => Lambda(Some(x), bind))) orElse
            rss(bind).map(Lambda(op,_))
        case ErasableLambda(tp, bind) =>
            rss(tp).map(ErasableLambda(_, bind)) orElse
            rss(bind).map(ErasableLambda(tp,_))
        case Fix(op, bind) => 
            op.flatMap(rss(_).map(x => Fix(Some(x), bind))) orElse
            rss(bind).map(Fix(op,_))
        case LetIn(op, v1, bind) =>
            op.flatMap(rss(_).map(x => LetIn(Some(x), v1, bind))) orElse
            rss(v1).map(LetIn(op, _, bind)) orElse
            rss(bind).map(LetIn(op, v1, _))
        case MacroTypeDecl(tpe, bind) =>
            rss(tpe).map(MacroTypeDecl(_, bind)) orElse
            rss(bind).map(MacroTypeDecl(tpe, _))
        case MacroTypeInst(v1, args) =>
            def convert(a: (Boolean,Tree)) =  a match{
                case (a1,a2) => rss(a2).map(newA2 => (a1,newA2))
            }
            rss(v1).map(MacroTypeInst(_, args)) orElse
            mapFirst(args,convert).map(MacroTypeInst(v1,_))
        case NatMatch(t, t0, bind) =>
            rss(t).map(NatMatch(_,t0,bind)) orElse
            rss(t0).map(NatMatch(t,_,bind)) orElse
            rss(bind).map(NatMatch(t,t0,_))
        case EitherMatch(t, bind1, bind2) =>
            rss(t).map(EitherMatch(_,bind1,bind2)) orElse
            rss(bind1).map(EitherMatch(t,_,bind2)) orElse
            rss(bind2).map(EitherMatch(t,bind1,_))
        case Primitive(op, args) =>
            mapFirst2(args, rss(_)).map(Primitive(op,_))
        case ErasableApp(t1, t2) =>
            rss(t1).map(ErasableApp(_,t2)) orElse
            rss(t2).map(ErasableApp(t1,_))
        case Fold(tp, t) => 
            rss(tp).map(Fold(_,t)) orElse
            rss(t).map(Fold(tp,_))
        case Unfold(t, bind) =>
            rss(t).map(Unfold(_,bind)) orElse
            rss(bind).map(Unfold(t,_))
        case UnfoldPositive(t, bind) => 
            rss(t).map(UnfoldPositive(_,bind)) orElse
            rss(bind).map(UnfoldPositive(t,_))
        case Abs(t) => 
            rss(t).map(Abs(_))
        case TypeApp(t1, t2) => 
            rss(t1).map(TypeApp(_,t2)) orElse
            rss(t2).map(TypeApp(t1,_))
        case Error(s, op) => 
            op.flatMap(rss(_).map(newT => Error(s,Some(newT))))
            
        case NatType => None
        case BoolType => None
        case UnitType => None

        case SumType(t1, t2) => 
            rss(t1).map(SumType(_,t2)) orElse
            rss(t2).map(SumType(t1,_))
        case PiType(t1, bind) => 
            rss(t1).map(PiType(_,bind)) orElse
            rss(bind).map(PiType(t1,_))
        case SigmaType(t1, bind) =>
            rss(t1).map(SigmaType(_,bind)) orElse
            rss(bind).map(SigmaType(t1,_))
        case IntersectionType(t1, bind) => 
            rss(t1).map(IntersectionType(_,bind)) orElse
            rss(bind).map(IntersectionType(t1,_))
        case RefinementType(t1, bind) => 
            rss(t1).map(RefinementType(_,bind)) orElse
            rss(bind).map(RefinementType(t1,_))
        case RecType(n, bind) => 
            rss(n).map(RecType(_,bind)) orElse
            rss(bind).map(RecType(n,_))
        case PolyForallType(bind) =>
            rss(bind).map(PolyForallType(_))
        
        case BottomType => None
        case TopType => None

        case _ => throw new java.lang.Exception(s"Function `replaceSmallStep` is not implemented on $body (${body.getClass}).")
      }
    }
    */
  }
  
  def replaceFirstConditionalOnSuperTree(
    p: (Tree, Option[(Tree, Int)]) => Option[Tree], body: Tree,
    superTreeFilter: (Tree, Int) => Boolean, superTree: Option[(Tree, Int)] = None)
    (implicit rc: RunContext): 
    Option[Tree] = {
      p(body, superTree) match {
        case Some(value) => Some(value)
        case None => 
          def newSuperTree(index: Int) = Option.when( superTreeFilter(body, index) ){ (body, index) } orElse superTree

          def rfcs_(t: Tree, index: Int): Option[Tree] = replaceFirstConditionalOnSuperTree(p,t,superTreeFilter,newSuperTree(index))
          def rfcs(p: (Tree, Int)): Option[(Tree,Int)] = rfcs_(p._1, p._2).map((_, 0)) //Second argument will be unzipped and discarted
          
          val subTrees = body.subTrees().zipWithIndex
          val opOfListOfPairs = mapFirst2[(Tree, Int)](subTrees,rfcs)
          val (newSubTrees, _) = opOfListOfPairs.map(_.unzip).unzip //removes second argument from above
          newSubTrees.map(body.newSubTrees(_))
      }
  }

}