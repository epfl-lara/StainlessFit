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
    def newP[A](t: Tree, discarted: A): Option[Tree] = p(t)
    replaceFirstConditionalOnSuperTree(newP,body,(_,_) => false)
  }
  
  def replaceFirstConditionalOnSuperTree(
    p: (Tree, Option[(Tree, Int)]) => Option[Tree], body: Tree,
    superTreeFilter: (Tree, Int) => Boolean, superTree: Option[(Tree, Int)] = None)
    (implicit rc: RunContext): 
    Option[Tree] = {
      p(body, superTree) match {
        case result@Some(_) => result
        case None => 
          def newSuperTree(index: Int) = Option.when( superTreeFilter(body, index) ){ (body, index) } orElse superTree

          def rfcs_(t: Tree, index: Int): Option[Tree] = replaceFirstConditionalOnSuperTree(p,t,superTreeFilter,newSuperTree(index))
          def rfcs(p: (Tree, Int)): Option[(Tree,Int)] = rfcs_(p._1, p._2).map((_, 0)) //Second argument will be unzipped and discarted
          
          val (children, reconstruct) = body.deconstruct
          val subTrees = children.zipWithIndex
          val opOfListOfPairs = mapFirst2[(Tree, Int)](subTrees, rfcs)
          val (newSubTrees, _) = opOfListOfPairs.map(_.unzip).unzip //removes second argument from above
          newSubTrees.map(reconstruct)
      }
  }

}