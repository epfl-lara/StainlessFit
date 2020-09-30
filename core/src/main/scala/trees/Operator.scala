/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core
package trees

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
