package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import extraction._
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, Neq => IRNeq,
  Eq => IREq, Lt => IRLt, Gt => IRGt, Leq => IRLeq, Geq => IRGeq, Nop => IRNop,
  Plus => IRPlus, Minus => IRMinus, Mul => IRMul, Div => IRDiv,
  BooleanLiteral => IRBooleanLiteral, UnitLiteral => IRUnitLiteral,
  NatType => IRNatType, UnitType => IRUnitType, _}

import codegen.llvm._
import codegen.utils.{Identifier => _, _}

class CodeGen(val rc: RunContext) {

    def genLLVM(tree: Tree, isMainModule: Boolean, moduleName: String): Module = {
        cgModule(tree, moduleName)
    }

    def cgModule(inputTree: Tree, moduleName: String): Module = {

      val (defFunctions, mainBody) = extractDefFun(inputTree)

      val fh = new FunctionHandler(rc)
      val emptyFunctions: List[(Function, LocalHandler, Tree)] = defFunctions.map(defFun => translateDefFunction(defFun, fh))
      val functions = emptyFunctions.map{ case (fun, lh, funBody) => cgFunction(fun, lh, funBody, fh) }

      val mainFunction = Function(IRNatType, Global("main"), Nil)
      val main = cgFunction(mainFunction, new LocalHandler(rc), mainBody, fh, true)

      Module(
        moduleName,
        main,
        functions)
    }

    def translateDefFunction(defFun: DefFunction, fh: FunctionHandler): (Function, LocalHandler, Tree) = {
      val DefFunction(args, optReturnType, _, bind, _) = defFun

      val params = args.toList.map{
        case TypedArgument(id, tpe) => (id, ParamDef(translateType(tpe), Local(id.name)))
        case arg => rc.reporter.fatalError(s"Unexpected type for arg $arg")
      }

      val (funId, body) = extractBody(bind)

      val returnType = translateType(optReturnType.getOrElse(rc.reporter.fatalError("No return type found")))

      val function = Function(returnType, Global(funId.name), params.unzip._2)
      fh.add(funId, function)

      val lh = new LocalHandler(rc)
      lh.add(params)

      (function, lh, body)
    }

    def cgFunction(function: Function, lh: LocalHandler, body: Tree, fh: FunctionHandler, isMain: Boolean = false): Function = {

      val initBlock = lh.newBlock("Entry")
      val returnType = if(isMain) typeOf(body)(lh, fh) else function.returnType

      val end = if(isMain) lh.freshLabel("Print.and.exit") else lh.freshLabel("End")
      val result = lh.freshLocal("result")

      val prep = function.returnType match {
        case EitherType(_, _) => List(Malloc(result, lh.dot(result, "malloc"), function.returnType), NoOp)
        case _ => Nil
      }

      val (entryBlock, phi) = codegen(body, initBlock <:> prep, Some(end), Some(result), returnType)(lh, function, fh)
      function.add(entryBlock)

      val endBlock = lh.newBlock(end)

      val (lastBlock, returnValue) = if(isMain){

        val resultPrinter = new ResultPrinter(rc)
        (resultPrinter.customPrint(endBlock, result, returnType, false, None)(lh, function), Value(Nat(0)))
      } else {
        (endBlock, Value(result))
      }

      val ret = Return(returnValue, function.returnType)
      function.add(lastBlock <:> ret)

      function
    }

    def extractDefFun(t: Tree): (List[DefFunction], Tree) = t match {
      case defFun @ DefFunction(_, _, _, _, nested) => {  //DefFunction(_, _, _, _, Bind(fid, body))
        val (defs, rest) = extractDefFun(nested)
        (defFun +: defs, rest)
      }
      case bind: Bind => extractDefFun(extractBody(bind)._2)

      case Var(_) => (Nil, NatLiteral(BigInt(0)))
      case rest => (Nil, rest)
    }

    def extractBody(bind: Tree): (Identifier, Tree) = bind match {
      case Bind(id, rec: Bind) => extractBody(rec)
      case Bind(id, body) => (id, body)
      case _ => rc.reporter.fatalError(s"Couldn't find the body in $bind")
    } //Binds(bind: Bind): Option(Seq[Identifier], Tree) otherwise only the first identifier is returned

    def translateOp(op: Operator): Op = op match {
      case Not => IRNot
      case And => IRAnd
      case Or => IROr
      case Neq => IRNeq
      case Eq => IREq
      case Lt => IRLt
      case Gt => IRGt
      case Leq => IRLeq
      case Geq => IRGeq
      case Nop => IRNop
      case Plus => IRPlus
      case Minus => IRMinus
      case Mul => IRMul
      case Div => IRDiv

      case _ => rc.reporter.fatalError("Not yet implemented")
    }

    def translateType(tpe: Tree): Type = tpe match {
      case BoolType => BooleanType
      case NatType => IRNatType
      case UnitType => IRUnitType
      case Bind(_, rest) => translateType(rest) //TODO Is this necessary
      case SigmaType(tpe, bind) => PairType(translateType(tpe), translateType(bind))
      case SumType(leftType ,rightType) => EitherType(translateType(leftType), translateType(rightType))
      case _ => rc.reporter.fatalError(s"Unable to translate type $tpe")
    }

    def translateValue(t: Tree)(implicit lh: LocalHandler): Value = t match {
      case BooleanLiteral(b) => Value(IRBooleanLiteral(b))
      case NatLiteral(n) => Value(Nat(n))
      case UnitLiteral => Value(Nat(0))
      case Var(id) => Value(lh.getLocal(id))
      case _ => rc.reporter.fatalError(s"This tree isn't a value: $t")
    }

    def cgValue(tpe: Type, value: Value, next: Option[Label], toAssign: Option[Local])
    (implicit lh: LocalHandler): List[Instruction] = {
      val jump = jumpTo(next)
      val assign = Assign(assignee(toAssign), tpe, value)
      if(toAssign.isEmpty && jump.isEmpty) rc.reporter.fatalError("Unexpected control flow during codegen")

      assign +: jump
    }

    def isValue(t: Tree): Boolean = t match {
      case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral | Var(_) => true
      case _ => false
    }

    def flattenPrimitive(t: Tree): List[Tree] = t match {
      case Primitive(op, args) => args.flatMap{
        case Primitive(op2, args2) if op2 == op => flattenPrimitive(Primitive(op2, args2))
        case other => List(other)
      }

      case _ => rc.reporter.fatalError(s"flattenPrimitive is not defined for $t")
    }

    def flattenApp(t: Tree): (Identifier, List[Tree]) = t match {
      case App(Var(id), arg) => (id, List(arg))
      case App(recApp @ App(_, _), arg) => {
        val (id, otherArgs) = flattenApp(recApp)
        (id , otherArgs :+ arg)
      }

      case _ => rc.reporter.fatalError(s"flattenApp is not defined fo $t")
    }

    def typeOf(t: Tree)(implicit lh: LocalHandler, fh: FunctionHandler): Type = t match {
      case BooleanLiteral(_) => BooleanType
      case NatLiteral(_) => IRNatType
      case UnitLiteral => IRUnitType
      case Var(id) => lh.getType(id)
      case LetIn(_, _, Bind(_, rest)) => typeOf(rest)
      case Primitive(op, _) => translateOp(op).returnType
      case IfThenElse(_, thenn, _) => typeOf(thenn)

      case app @ App(_, _) => fh.getReturnType(flattenApp(app)._1)

      case Pair(first, second) => PairType(typeOf(first), typeOf(second))

      case First(pair) => typeOf(pair) match {
        case tpe @ FunctionReturnType(_) => FirstType(tpe)
        case PairType(firstType, _) => firstType
        case nested @ FirstType(_) => FirstType(nested)
        case nested @ SecondType(_) => FirstType(nested)
        case other => rc.reporter.fatalError(s"Unexpected operation: calling First on type $other")
      }
      case Second(pair) => typeOf(pair) match {
        case tpe @ FunctionReturnType(_) => SecondType(tpe)
        case PairType(_, secondType) => secondType
        case nested @ FirstType(_) => SecondType(nested)
        case nested @ SecondType(_) => SecondType(nested)
        case other => rc.reporter.fatalError(s"Unexpected operation: calling Second on type $other")
      }

      case LeftTree(either) => LeftType(typeOf(either))
      case RightTree(either) => RightType(typeOf(either))
      case EitherMatch(_, t1, t2) => {
        (typeOf(t1), typeOf(t2)) match {
          case (leftType, rightType) if leftType == rightType => leftType
          case (LeftType(innerLeft), RightType(innerRight)) => EitherType(innerLeft, innerRight)
          case (RightType(innerRight), LeftType(innerLeft)) => EitherType(innerLeft, innerRight)
          case (leftType, rightType) =>
            rc.reporter.fatalError(s"EitherMatch returns different types: left => $leftType, right => $rightType")
        }
      }

      case Bind(_, body) => typeOf(body)

      case _ => rc.reporter.fatalError(s"Result type not yet implemented for $t")
    }

    def cgFunctionBodyCall(call: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
      (implicit lh: LocalHandler, f: Function, fh: FunctionHandler): (Block, List[Instruction]) = {

        val (funId, flatArgs) = flattenApp(call)
        val init: (Block, List[Value]) = (block, Nil)

        val (currentBlock, values) = flatArgs.zipWithIndex.foldLeft(init){
          case ((currentBlock, values), (arg, index)) => {
            val temp = lh.freshLocal(s"arg_$index")
            val argType = fh.getArgType(funId, index)

            val prepArg = argType match {
              case EitherType(_, _) => List(Malloc(temp, lh.dot(temp, "malloc"), argType), NoOp)
              case _ => Nil
            }

            val (nextBlock, phi) = codegen(arg, currentBlock <:> prepArg, None, Some(temp), argType)
            (nextBlock <:> phi, values :+ Value(temp))
          }
        }

        val result = assignee(toAssign)
        val jump = jumpTo(next)

        (currentBlock <:> Call(result, Global(funId.name), values) <:> NoOp <:> jump, Nil)
    }

    def cgEitherChoose(either: Local, eitherType: Type, chooseLeft: Label, chooseRight: Label)
      (implicit lh: LocalHandler): List[Instruction] = {
      val eitherTypePtr = lh.dot(either, "type.gep")
      val eitherCond = lh.dot(either, "type")

      val choose = List(
        GepToIdx(eitherTypePtr, eitherType, Value(either), Some(0)),
        Load(eitherCond, BooleanType, eitherTypePtr),
        Branch(Value(eitherCond), chooseRight, chooseLeft)  //false => left
      )
      choose
    }

    def cgAlternatives(trueLabel: Label, trueBody: Tree, falseLabel: Label, falseBody: Tree,
      after: Label, toAssign: Option[Local], resultType: Type)
      (implicit lh: LocalHandler, f: Function, fh: FunctionHandler): List[Instruction] = {
        val assign = assignee(toAssign)

        val (trueLocal, falseLocal) = resultType match {
          case EitherType(_, _) => (assign, assign)
          case _ => (lh.freshLocal("phi"), lh.freshLocal("phi"))
        }

        val tBlock = lh.newBlock(trueLabel)
        val (trueBlock, truePhi) = codegen(trueBody, tBlock, Some(after), Some(trueLocal), resultType)
        f.add(trueBlock)

        val fBlock = lh.newBlock(falseLabel)
        val (falseBlock, falsePhi) = codegen(falseBody, fBlock, Some(after), Some(falseLocal), resultType)
        f.add(falseBlock)

        val nextPhi = resultType match {
          case EitherType(_, _) => Nil
          case _ => List(Phi(assign, resultType, List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label))))
        }

        truePhi ++ falsePhi ++ nextPhi
    }

    def getLeft(either: Local, tpe: EitherType)(implicit lh: LocalHandler): (Local, List[Instruction]) = {
      val eitherLeftPtr = lh.dot(either, "left.gep")
      val leftLocal = lh.dot(either, "left")
      val prepLeft = List(
        GepToIdx(eitherLeftPtr, tpe, Value(either), Some(1)),
        Load(leftLocal, tpe.leftType, eitherLeftPtr))
        (leftLocal, prepLeft)
    }

    def getRight(either: Local, tpe: EitherType)(implicit lh: LocalHandler): (Local, List[Instruction]) = {
      val eitherRightPtr = lh.dot(either, "right.gep")
      val rightLocal = lh.dot(either, "right")
      val prepRight = List(
        GepToIdx(eitherRightPtr, tpe, Value(either), Some(2)),
        Load(rightLocal, tpe.rightType, eitherRightPtr))
        (rightLocal, prepRight)
    }

    def filterErasable(t: Tree): Tree = t match {
      case
        MacroTypeDecl(_, _) |
        MacroTypeInst(_, _) |
        ErasableApp(_, _) |
        Refl(_, _) |
        Fold(_, _) |
        Unfold(_, _) |
        UnfoldPositive(_, _) |
        DefFunction(_, _, _, _, _) |
        ErasableLambda(_, _) |
        Abs(_) |
        TypeApp(_, _) |
        Because(_, _) => rc.reporter.fatalError(s"This tree should have been erased: $t")

      case _ => t
    }

    def assignee(toAssign: Option[Local])(implicit lh: LocalHandler) = toAssign getOrElse lh.freshLocal
    def jumpTo(next: Option[Label]) = next.toList.map(label => Jump(label))

    def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local], resultType: Type)
      (implicit lh: LocalHandler, f: Function, fh: FunctionHandler): (Block, List[Instruction]) =

      filterErasable(inputTree) match {

        case value if isValue(value) => (block <:> cgValue(resultType, translateValue(value), next, toAssign), Nil)

        case call @ App(_, _) => cgFunctionBodyCall(call, block, next, toAssign)

        case Pair(first, second) => {
          val pair = assignee(toAssign)
          val firstLocal = lh.dot(pair, "first")
          val secondLocal = lh.dot(pair, "second")

          val t3 = lh.dot(pair, "malloc")

          val (firstType, secondType) = resultType match {
            case PairType(f, s) => (f, s)
            case other => rc.reporter.fatalError(s"Expected type is $resultType but value has type Pair(_, _)")
          }
          val pairType = PairType(firstType, secondType)

          val malloc = Malloc(pair, t3, pairType) //will assign toAssign

          val (firstBlock, firstPhi) = codegen(first, block <:> malloc <:> NoOp, None, Some(firstLocal), firstType)
          val (secondBlock, secondPhi) = codegen(second, firstBlock <:> firstPhi, None, Some(secondLocal), secondType)

          val (firstPtr, secondPtr) = (lh.dot(pair, "first.gep"), lh.dot(pair, "second.gep"))

          val initialise = List(
            GepToIdx(firstPtr, pairType, Value(pair), Some(0)),
            Store(Value(firstLocal), firstType, firstPtr),
            NoOp,
            GepToIdx(secondPtr, pairType, Value(pair), Some(1)),
            Store(Value(secondLocal), secondType, secondPtr),
            NoOp
          )

          (secondBlock <:> secondPhi <:> initialise <:> jumpTo(next), Nil)
        }

        case First(pair) => { //TODO refactor first and second since they are identical?
          val pairLocal = lh.freshLocal("pair")
          val pairType = typeOf(pair)
          val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal), pairType)

          val assignLocal = assignee(toAssign)
          val firstPtr = lh.dot(assignLocal, "first.gep")

          val prep = List(
            GepToIdx(firstPtr, pairType, Value(pairLocal), Some(0)),
            Load(assignLocal, resultType, firstPtr),
            NoOp
          )

          (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
        }

        case Second(pair) => {

          val pairLocal = lh.freshLocal("pair")
          val pairType = typeOf(pair)
          val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal), pairType)

          val assignLocal = assignee(toAssign)

          val secondPtr = lh.dot(pairLocal, "second.gep")

          val prep = List(
            GepToIdx(secondPtr, pairType, Value(pairLocal), Some(1)),
            Load(assignLocal, resultType, secondPtr),
            NoOp
          )

          (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
        }

        case LetIn(optTpe, valueBody, Bind(newVar, rest)) => {
            val local = lh.freshLocal(newVar)

            val valueTpe = optTpe match {
              case Some(tpe) => translateType(tpe)
              case None => typeOf(valueBody)
            }

            val prep = valueTpe match {
              case EitherType(_, _) => List(Malloc(local, lh.dot(local, "malloc"), valueTpe), NoOp)
              case _ => Nil
            }

            val (tempBlock, phi) = codegen(valueBody, block <:> prep, None, Some(local), valueTpe)
            lh.add(newVar, ParamDef(valueTpe, local))
            codegen(rest, tempBlock <:> phi, next, toAssign, resultType)
        }

        case IfThenElse(cond, thenn, elze) => {

          val condLocal = lh.freshLocal("cond")

          val trueLabel = lh.dot(block.label, "then")
          val falseLabel = lh.dot(block.label, "else")
          val afterLabel = lh.dot(block.label, "after")

          val (condPrep, condPhi) = codegen(cond, block, None, Some(condLocal), BooleanType)

          val parentBlock =
            condPrep <:>
            condPhi <:>
            Branch(Value(condLocal), trueLabel, falseLabel)

          f.add(parentBlock)

          val afterPhi = cgAlternatives(trueLabel, thenn, falseLabel, elze, afterLabel, toAssign, resultType)

          val jump = jumpTo(next)
          (lh.newBlock(afterLabel) <:> afterPhi <:> jump, Nil)
        }

        case Primitive(op, args) => {
          val init: (Block, List[Value]) = (block, Nil)
          val (currentBlock, values) = args.map((_, lh.freshLocal("temp"))).foldLeft(init){
            case ((currentBlock, values), (arg, temp)) => {
              val (nextBlock, phi) = codegen(arg, currentBlock, None, Some(temp), typeOf(arg))
              (nextBlock <:> phi, values :+ Value(temp))
            }
          }

          val jump = jumpTo(next)

          val operation = values match {
            case List(operand) => UnaryOp(translateOp(op), assignee(toAssign), operand)
            case List(leftOp, rightOp) => BinaryOp(translateOp(op), assignee(toAssign), leftOp, rightOp)
            case other => rc.reporter.fatalError(s"Unexpected number of arguments for operator $op. Expected 1 or 2 but was ${other.size}")
          }

          (currentBlock <:> operation <:> jump, Nil)
        }

        case EitherMatch(scrut, t1, t2) => {
          val (varLeft, bodyLeft) = extractBody(t1)
          val (varRight, bodyRight) = extractBody(t2)

          val scrutLocal = lh.freshLocal("scrut")
          val scrutType = typeOf(scrut)
          val (currentBlock, scrutPhi) = codegen(scrut, block, None, Some(scrutLocal), scrutType)

          scrutType match {
            case LeftType(innerType) => {
              lh.add(varLeft, ParamDef(innerType, scrutLocal))
              codegen(bodyLeft, currentBlock <:> scrutPhi, next, toAssign, resultType)
            }

            case RightType(innerType) => {
              lh.add(varRight, ParamDef(innerType, scrutLocal))
              codegen(bodyRight, currentBlock <:> scrutPhi, next, toAssign, resultType)
            }

            case tpe @ EitherType(leftType, rightType) => {
              val leftLabel = lh.dot(block.label, "match.left")
              val rightLabel = lh.dot(block.label, "match.right")
              val afterLabel = lh.dot(block.label, "after")

              val (leftLocal, prepLeft) = getLeft(scrutLocal, tpe)
              lh.add(varLeft, ParamDef(leftType, leftLocal))

              val (rightLocal, prepRight) = getRight(scrutLocal, tpe)
              lh.add(varRight, ParamDef(rightType, rightLocal))

              val choose = cgEitherChoose(scrutLocal, tpe, leftLabel, rightLabel)
              f.add(currentBlock <:> scrutPhi <:> prepLeft <:> prepRight <:> choose)

              val afterPhi = cgAlternatives(leftLabel, bodyLeft, rightLabel, bodyRight, afterLabel, toAssign, resultType)

              (lh.newBlock(afterLabel) <:> afterPhi <:> jumpTo(next), Nil)
            }
          }
        }

        case LeftTree(either) => {

          val assignLocal = assignee(toAssign)
          val leftLocal = lh.freshLocal("left")

          val eitherValuePtr = lh.dot(assignLocal, "left.value.gep")
          val eitherTypePtr = lh.dot(assignLocal, "left.type.gep")

          val (currentBlock, phi) = (toAssign, resultType) match {
            case (Some(local), EitherType(leftType, _)) => {

              val assign = List(
                GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                Store(Value(IRBooleanLiteral(false)), BooleanType, eitherTypePtr),
                NoOp,
                GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(1)),
                Store(Value(leftLocal), leftType, eitherValuePtr),
                NoOp)

                val (prepBlock, p) = codegen(either, block, None, Some(leftLocal), leftType)
                (prepBlock <:> p <:> assign, Nil)
            }

            case (Some(local), LeftType(innerType)) => codegen(either, block, None, Some(local), innerType)
            //case (None, _) => codegen(either, block, None, None, resultType)
            case (opt, other) => rc.reporter.fatalError(s"Found LeftTree but expected $other when assigning $opt")
            //TODO malloc a temp variable when there is nothing to assign?
          }

          (currentBlock <:> phi <:> jumpTo(next), Nil)
        }

        case RightTree(either) => {

          val assignLocal = assignee(toAssign)
          val rightLocal = lh.freshLocal("right")

          val eitherValuePtr = lh.dot(assignLocal, "right.value.gep")
          val eitherTypePtr = lh.dot(assignLocal, "right.type.gep")

          val (currentBlock, phi) = (toAssign, resultType) match {
            case (Some(local), EitherType(_, rightType)) => {

              val assign = List(
                GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                Store(Value(IRBooleanLiteral(true)), BooleanType, eitherTypePtr),
                NoOp,
                GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(2)),
                Store(Value(rightLocal), rightType, eitherValuePtr),
                NoOp)

                val (prepBlock, p) = codegen(either, block, None, Some(rightLocal), rightType)
                (prepBlock <:> p <:> assign, Nil)
            }

            case (Some(local), RightType(innerType)) => codegen(either, block, None, Some(local), innerType)
            // case (None, _) => codegen(either, block, None, None, resultType)
            case (opt, other) => rc.reporter.fatalError(s"Found RightTree but expected $other when assigning $opt")
            //TODO malloc a temp variable when there is nothing to assign?
          }

          (currentBlock <:> phi <:> jumpTo(next), Nil)
        }
        case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
    }
}
