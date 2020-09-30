package stainlessfit
package core
package trees

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
