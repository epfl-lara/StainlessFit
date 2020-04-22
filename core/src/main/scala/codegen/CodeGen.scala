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

class CodeGen(implicit val rc: RunContext) extends Phase[Module] {
  def transform(t: Tree): (Tree, Module) = (t, CodeGen.genLLVM(t, true, rc.config.file.getName()))
}

object CodeGen {
    def genLLVM(tree: Tree, isMainModule: Boolean, moduleName: String)(implicit rc: RunContext): Module = {

        def cgModule(inputTree: Tree): Module = {

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
            case EitherType(_, _) => List(Malloc(result, lh.dot(result, "malloc"), function.returnType))
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
        } //Binds(bind: Bind): Option(Seq[Identifier], Tree) unapply est utilisé dans un pattern match

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

          case _ => rc.reporter.fatalError(s"Result type not yet implemented for $t")
        }

        def cgFunctionBodyCall(call: Tree, block: Block, next: Option[Label], toAssign: Option[Local])
          (implicit lh: LocalHandler, f: Function, fh: FunctionHandler): (Block, List[Instruction]) = {

            val (funId, flatArgs) = flattenApp(call)
            val init: (Block, List[Value]) = (block, Nil)

            val (currentBlock, values) = flatArgs.zipWithIndex.foldLeft(init){
              case ((currentBlock, values), (arg, index)) => {
                val temp = lh.freshLocal(s"arg_$index")
                val (nextBlock, phi) = codegen(arg, currentBlock, None, Some(temp), fh.getArgType(funId, index))
                (nextBlock <:> phi, values :+ Value(temp))
              }
            }

            val result = assignee(toAssign)
            val jump = jumpTo(next)

            (currentBlock <:> Call(result, Global(funId.name), values) <:> NoOp <:> jump, Nil)
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

            case value if isValue(value) => (block <:> cgValue(typeOf(value), translateValue(value), next, toAssign), Nil)

            case call @ App(_, _) => cgFunctionBodyCall(call, block, next, toAssign)

            case Pair(first, second) => {
              val pair = assignee(toAssign)
              val firstLocal = lh.dot(pair, "first")
              val secondLocal = lh.dot(pair, "second")

              val t3 = lh.dot(pair, "malloc")

              val pairType = typeOf(inputTree)
              val (firstType, secondType) = resultType match {
                case PairType(f, s) => (f, s)
                case other => rc.reporter.fatalError(s"Expected type is $resultType but value has type Pair(_, _)")
              }

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
                  case EitherType(_, _) => List(Malloc(local, lh.dot(local, "malloc"), valueTpe))
                  case _ => Nil
                }

                val (tempBlock, phi) = codegen(valueBody, block <:> prep, None, Some(local), valueTpe)
                lh.add(newVar, ParamDef(valueTpe, local))
                codegen(rest, tempBlock <:> phi, next, toAssign, resultType)
            }

            case IfThenElse(cond, thenn, elze) => {

              val condLocal = lh.freshLocal("cond")

              val assign = assignee(toAssign)

              val (trueLocal, falseLocal) = resultType match {
                case EitherType(_, _) => (assign, assign)
                case _ => (lh.freshLocal("phi"), lh.freshLocal("phi"))
              }
              val tBlock = lh.newBlock("then")
              val fBlock = lh.newBlock("else")

              val afterLocal = lh.freshLocal()
              val afterBlock = lh.newBlock("after")

              val (condPrep, condPhi) = codegen(cond, block, None, Some(condLocal), BooleanType)

              val (trueBlock, truePhi) = codegen(thenn, tBlock, Some(afterBlock.label), Some(trueLocal), resultType)
              f.add(trueBlock)

              val (falseBlock, falsePhi) = codegen(elze, fBlock, Some(afterBlock.label), Some(falseLocal), resultType)
              f.add(falseBlock)

              val parentBlock =
                condPrep <:>
                condPhi <:>
                Branch(Value(condLocal), tBlock.label, fBlock.label)

              f.add(parentBlock)

              val nextPhi = truePhi ++ falsePhi ++ (resultType match {
                case EitherType(_, _) => Nil
                case _ => List(Phi(assign, resultType, List((trueLocal, trueBlock.label), (falseLocal, falseBlock.label))))
              })

              val jump = jumpTo(next)
              (afterBlock <:> nextPhi <:> jump, Nil)
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

            case EitherMatch(t, t1, t2) => ???

            case LeftTree(either) => {

              val assignLocal = assignee(toAssign)
              val leftLocal = lh.freshLocal("left")

              val eitherValuePtr = lh.dot(assignLocal, "left.value.gep")
              val eitherTypePtr = lh.dot(assignLocal, "left.type.gep")

              val (currentBlock, phi) = (toAssign, resultType) match {
                case (Some(local), EitherType(_, _)) => {

                  val prep = List(
                    GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                    Store(Value(IRBooleanLiteral(false)), BooleanType, eitherTypePtr),
                    NoOp,
                    GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(1)),
                    Store(Value(leftLocal), typeOf(either), eitherValuePtr),
                    NoOp)

                    val (b, p) = codegen(either, block, None, Some(leftLocal), resultType)
                    (b <:> prep, p)
                }

                case (Some(local), _) => codegen(either, block, None, Some(local), resultType)
                case (None, EitherType(_, _)) => ??? //TODO malloc a temp variable?
                case (None, _) => codegen(either, block, None, None, resultType)
              }

              (currentBlock <:> phi <:> jumpTo(next), Nil)
            }
            case RightTree(either) => {

              val assignLocal = assignee(toAssign)
              val rightLocal = lh.freshLocal("right")

              val eitherValuePtr = lh.dot(assignLocal, "right.value.gep")
              val eitherTypePtr = lh.dot(assignLocal, "right.type.gep")

              val (currentBlock, phi) = (toAssign, resultType) match {
                case (Some(local), EitherType(_, _)) => {

                  val prep = List(
                    GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                    Store(Value(IRBooleanLiteral(true)), BooleanType, eitherTypePtr),
                    NoOp,
                    GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(2)),
                    Store(Value(rightLocal), typeOf(either), eitherValuePtr),
                    NoOp)

                    val (b, p) = codegen(either, block, None, Some(rightLocal), resultType)
                    (b <:> prep, p)
                }

                case (Some(local), _) => codegen(either, block, None, Some(local), resultType)
                case (None, EitherType(_, _)) => ??? //TODO malloc a temp variable?
                case (None, _) => codegen(either, block, None, None, resultType)
              }

              (currentBlock <:> phi <:> jumpTo(next), Nil)
            }
            case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
          }

        cgModule(tree)
    }
}
