package stainlessfit
package core
package codegen

import trees._
import TreeBuilders._
import util.RunContext
import extraction._
import codegen.llvm.IR.{And => IRAnd, Or => IROr, Not => IRNot, Neq => IRNeq,
  Eq => IREq, Lt => IRLt, Gt => IRGt, Leq => IRLeq, Geq => IRGeq,
  Plus => IRPlus, Minus => IRMinus, Mul => IRMul, Div => IRDiv,
  BooleanLiteral => IRBooleanLiteral, UnitLiteral => IRUnitLiteral,
  NatType => IRNatType, UnitType => IRUnitType, _}

import codegen.llvm._
import codegen.utils._

class CodeGen(val rc: RunContext) {

    def genLLVM(tree: Tree, isMainModule: Boolean, moduleName: String): Module = {
        cgModule(tree, moduleName)
    }

    def cgModule(inputTree: Tree, moduleName: String): Module = {

      val globalHandler = new GlobalHandler(rc)
      val mainFunction = CreateMain(globalHandler.freshGlobal("main"))
      val main = cgMain(mainFunction, inputTree, globalHandler)

      Module(
        moduleName,
        main,
        globalHandler.getLambdas()
      )
    }

    def cgMain(mainFun: Function, body: Tree, globalHandler: GlobalHandler): Function = {
      val lh = new LocalHandler(rc)
      val initBlock = lh.newBlock("Entry")
      val end = lh.freshLabel("Print.and.exit")

      val mainBody = filterErasable(body)
      val returnType = typeOf(mainBody)(lh, globalHandler, Map.empty)
      val result = lh.freshLocal("result")

      val prep = preAllocate(result, returnType)(lh)

      val (entryBlock, phi) = codegen(mainBody, initBlock <:> prep, Some(end), Some(result), returnType)(lh, mainFun, globalHandler)
      mainFun.add(entryBlock)

      val endBlock = lh.newBlock(end)
      val resultPrinter = new ResultPrinter(rc)
      val lastBlock = resultPrinter.customPrint(endBlock, result, returnType, false, None)(lh, mainFun)
      val returnValue = Value(Nat(0))

      mainFun.add(lastBlock <:> Return(Value(Nat(0)), IRNatType))

      mainFun
    }

    def cgFunction(function: Function, lh: LocalHandler, body: Tree, globalHandler: GlobalHandler,
        firstInstructions: List[Instruction] = Nil, isMain: Boolean = false, isTopLevel: Boolean = false): Function = {

      val initBlock = lh.newBlock("Entry") <:> firstInstructions
      val filteredBody = filterErasable(body)
      val returnType = function.returnType

      val end = lh.freshLabel("End")
      val result = lh.freshLocal("result")

      val prep = preAllocate(result, function.returnType)(lh)

      val (entryBlock, phi) = codegen(filteredBody, initBlock <:> prep, Some(end), Some(result), returnType)(lh, function, globalHandler)
      function.add(entryBlock)

      val endBlock = lh.newBlock(end)

      val ret = Return(Value(result), returnType)
      function.add(endBlock <:> ret)

      function
    }

    def extractBody(bind: Tree): (Identifier, Tree) = bind match {
      case Bind(id, rec: Bind) => extractBody(rec)
      case Bind(id, body) => (id, body)
      case _ => rc.reporter.fatalError(s"Couldn't find the body in $bind")
    } //Binds(bind: Bind): Option(Seq[Identifier], Tree) otherwise only the first identifier is returned

    def extractFreeVariables(t: Tree)(implicit closedVariables: List[Identifier]): List[Identifier] = t match {
      case Var(id) if !closedVariables.contains(id) => List(id)
      case LetIn(_, _, Bind(id, rest)) => extractFreeVariables(rest)(id +: closedVariables)

      case Primitive(op, args) => args.flatMap(arg => extractFreeVariables(arg))

      case IfThenElse(cond, thenn, elze) =>
        extractFreeVariables(cond) ++
        extractFreeVariables(thenn) ++
        extractFreeVariables(elze)

      case app @ App(_, _) => {
        val (_, flatArgs) = flattenApp(app)
        flatArgs.flatMap(arg => extractFreeVariables(arg))
      }

      case Pair(first, second) => extractFreeVariables(first) ++ extractFreeVariables(second)
      case First(pair) => extractFreeVariables(pair)
      case Second(pair) => extractFreeVariables(pair)
      case LeftTree(either) => extractFreeVariables(either)
      case RightTree(either) => extractFreeVariables(either)
      case Bind(_, body) => extractFreeVariables(body)
      case _ => Nil
    }

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
      case Plus => IRPlus
      case Minus => IRMinus
      case Mul => IRMul
      case Div => IRDiv

      case _ => rc.reporter.fatalError(s"Unable to translate operator $op")
    }

    def translateType(tpe: Tree): Type = tpe match {
      case BoolType => BooleanType
      case NatType => IRNatType
      case UnitType => IRUnitType
      case Bind(_, rest) => translateType(rest)
      case SigmaType(tpe, bind) => PairType(translateType(tpe), translateType(bind))
      case PiType(argType, Bind(_, retType)) => LambdaType(translateType(argType), translateType(retType))
      case SumType(leftType ,rightType) => EitherType(translateType(leftType), translateType(rightType))
      case RefinementType(typee, _) => translateType(typee)
      case _ => rc.reporter.fatalError(s"Unable to translate type $tpe")
    }

    def translateValue(t: Tree, tpe: Type)(implicit lh: LocalHandler, globalHandler: GlobalHandler): Value = t match {
      case BooleanLiteral(b) => Value(IRBooleanLiteral(b))
      case NatLiteral(n) => Value(Nat(n))
      case UnitLiteral => Value(IRBooleanLiteral(false))
      case Var(id) => Value(lh.getLocal(id))
      case _ => rc.reporter.fatalError(s"This tree isn't a value: $t")
    }

    def flattenApp(t: Tree): (Identifier, List[Tree]) = t match {
      case App(Var(id), arg) => (id, List(arg))
      case App(recApp @ App(_, _), arg) => {
        val (id, otherArgs) = flattenApp(recApp)
        (id , otherArgs :+ arg)
      }

      case _ => rc.reporter.fatalError(s"flattenApp is not defined fo $t")
    }

    def typeOfOperand(op: Operator): Type = op match {
      case Not => BooleanType
      case And => BooleanType
      case Or => BooleanType

      case Neq => IRNatType
      case Eq => IRNatType
      case Lt => IRNatType
      case Gt => IRNatType
      case Leq => IRNatType
      case Geq => IRNatType

      case Plus => IRNatType
      case Minus => IRNatType
      case Mul => IRNatType
      case Div => IRNatType

      case _ => rc.reporter.fatalError(s"Unable to determine the operand type of $op")
    }

    def typeOf(t: Tree)(implicit lh: LocalHandler, globalHandler: GlobalHandler, helper: Map[Identifier, Type]): Type = t match {
      case BooleanLiteral(_) => BooleanType
      case NatLiteral(_) => IRNatType
      case UnitLiteral => IRUnitType
      case Error(_, optType) => {
        optType match {
          case Some(tpe) => translateType(tpe)
          case None => IRUnitType
        }
      }
      case Var(id) => {
        if(helper.contains(id)){
          helper.get(id).get
        } else {
          lh.getType(id)
        }
      }
      case LetIn(optType, value, Bind(id, rest)) => {
        val valueType = optType match {
          case Some(tpe) => translateType(tpe)
          case None => typeOf(value)
        }

        val updatedHelper = helper + (id -> valueType)

        typeOf(rest)(lh, globalHandler, updatedHelper)
      }
      case Primitive(op, _) => translateOp(op).returnType
      case IfThenElse(_, thenn, elze) => {
        val thenType = typeOf(thenn)
        val elseType = typeOf(elze)

        (thenType, elseType) match {
          case (a, b) if a == b => thenType
          case (LeftType(a), RightType(b)) => EitherType(a, b)
          case (RightType(a), LeftType(b)) => EitherType(b, a)
        }
      }

      case Lambda(optArgType, Bind(argId, body)) => {
        val treeArgType = optArgType.getOrElse(rc.reporter.fatalError("Need to know the type of the argument"))
        val argType = translateType(treeArgType)
        val updatedHelper = helper + (argId -> argType)
        LambdaType(argType, typeOf(body)(lh, globalHandler, updatedHelper))
      }

      case app @ App(_, _) => {
        val (id, args) = flattenApp(app)

        val (startType, argsToFold) = (typeOf(Var(id)), args)

        argsToFold.foldLeft(startType){
          case (lambdaType, arg) => {
            val (_, retType) = getLambdaPrototype(lambdaType)
            retType
          }
        }
      }

      case Pair(first, second) => PairType(typeOf(first), typeOf(second))

      case First(pair) => typeOf(pair) match {
        case PairType(firstType, _) => firstType
        case nested @ FirstType(_) => FirstType(nested)
        case nested @ SecondType(_) => FirstType(nested)
        case other => rc.reporter.fatalError(s"Unexpected operation: calling First on type $other")
      }

      case Second(pair) => typeOf(pair) match {
        case PairType(_, secondType) => secondType
        case nested @ FirstType(_) => SecondType(nested)
        case nested @ SecondType(_) => SecondType(nested)
        case other => rc.reporter.fatalError(s"Unexpected operation: calling Second on type $other")
      }

      case LeftTree(either) => LeftType(typeOf(either))

      case RightTree(either) => RightType(typeOf(either))

      case EitherMatch(scrut, Bind(id1, t1), Bind(id2, t2)) => {
        val scrutType = typeOf(scrut)

        scrutType match {
          case LeftType(inner) => {
            val updatedHelper = helper + (id1 -> inner)
            typeOf(t1)(lh, globalHandler, updatedHelper)  //Assume the other branch returns the same type
          }
          case RightType(inner) => {
            val updatedHelper = helper + (id2 -> inner)
            typeOf(t2)(lh, globalHandler, updatedHelper)
          }
          case EitherType(leftType, rightType) =>  {
            val bind1 = helper + (id1 -> leftType)
            val bind2 = helper + (id2 -> rightType)

            val returnedByLeft = typeOf(t1)(lh, globalHandler, bind1)
            val returnedByRight = typeOf(t2)(lh, globalHandler, bind2)

            (returnedByLeft, returnedByRight) match {
              case (typeLeft, typeRight) if typeLeft == typeRight => typeLeft
              case (LeftType(innerLeft), RightType(innerRight)) => EitherType(innerLeft, innerRight)
              case (RightType(innerRight), LeftType(innerLeft)) => EitherType(innerLeft, innerRight)
              case (_, _) =>
                rc.reporter.fatalError(s"EitherMatch returns different types: left returns => $returnedByLeft, right returns => $returnedByRight")
            }
          }
        }
      }

      case Bind(_, body) => typeOf(body)

      case _ => rc.reporter.fatalError(s"TypeOf not yet implemented for $t")
    }

    def isValue(t: Tree): Boolean = t match {
      case BooleanLiteral(_) | NatLiteral(_) | UnitLiteral | Var(_) => true
      case _ => false
    }

    def cgValue(tpe: Type, value: Value, next: Option[Label], toAssign: Option[Local])
      (implicit lh: LocalHandler): List[Instruction] = {
        val jump = jumpTo(next)
        val assign = Assign(assignee(toAssign), tpe, value)

        assign +: jump
    }

    def cgLambdaCall(lambda: Local, args: List[Tree], block: Block, next: Option[Label], res: Local, argType: Type, retType: Type)
      (implicit lh: LocalHandler, f: Function, globalHandler: GlobalHandler): Block = {

        def applyOneArg(arg: Tree, res: Local, argType: Type, retType: Type): Block = {

          val argLocal = lh.freshLocal("arg")
          val prepArg = preAllocate(argLocal, argType)
          val (currentBlock, phi) = codegen(arg, block <:> prepArg, None, Some(argLocal), argType)

          val (prep, callName, envToPass) = if(lambda == f.recursiveLocal){
            (Nil, f.name, Value(Local(".raw.env")))
          } else {
            val (funLocal, loadFun) = getLambdaFunction(lambda, argType, retType)
            val (envLocal, loadEnv) = getLambdaEnv(lambda, argType, retType)
            (loadFun ++ loadEnv, funLocal, Value(envLocal))
          }

          currentBlock <:> phi <:> prep <:> Call(res, retType, callName, List(Value(argLocal)), List(argType), envToPass)
        }

        args match {
          case arg :: Nil =>  {
            val currentBlock = applyOneArg(arg, res, argType, retType) <:> jumpTo(next)
            currentBlock
          }

          case arg :: rest => {
            val tempRes = lh.freshLocal("nested.lambda")
            val currentBlock = applyOneArg(arg, tempRes, argType, retType)
            val (nextArgType, nextRetType) = getLambdaPrototype(retType)
            cgLambdaCall(tempRes, rest, currentBlock, next, res, nextArgType, nextRetType)
          }

          case Nil => block <:> jumpTo(next)
        }
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
      (implicit lh: LocalHandler, f: Function, globalHandler: GlobalHandler): List[Instruction] = {
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

    def accessedVariables(t: Tree): List[Identifier] = t match {
      case Var(id) => List(id)
      case app @ App(_, _) => {
        val (id, args) = flattenApp(app)
        id +: args.flatMap(arg => accessedVariables(arg))
      }
      case Pair(first, second) => accessedVariables(first) ++ accessedVariables(second)
      case First(pair) => accessedVariables(pair)
      case Second(pair) => accessedVariables(pair)

      case LetIn(_, value, Bind(id, rest)) => {
        (accessedVariables(value) ++ accessedVariables(rest)).filter(_ != id)
      }

      case Lambda(_, bind) => accessedVariables(bind)

      case IfThenElse(cond, thenn, elze) =>
        accessedVariables(cond) ++
        accessedVariables(thenn) ++
        accessedVariables(elze)

      case Primitive(_, args) => args.flatMap(arg => accessedVariables(arg))

      case EitherMatch(scrut, t1, t2) => {
        accessedVariables(scrut) ++ accessedVariables(t1) ++ accessedVariables(t2)
      }

      case LeftTree(either) => accessedVariables(either)
      case RightTree(either) => accessedVariables(either)

      case Bind(id, body) => accessedVariables(body).filter(_ != id)

      case _ => Nil
    }

    def cgLambda(lambdaBody: Tree, argId: Identifier, lambdaType: Type)
      (implicit lh: LocalHandler, globalHandler: GlobalHandler): (Global, List[Identifier], List[Type]) = {

      val newLambdaId = globalHandler.nextLambdaId()
      val lambdaGlobal = globalHandler.freshGlobal(newLambdaId)
      val (argType, retType) = getLambdaPrototype(lambdaType)

      val freeVariables = accessedVariables(lambdaBody).filter(freeVar => freeVar != argId && freeVar != newLambdaId)
      val freeTypes = freeVariables.map(freeVar => lh.getType(freeVar))

      val lambdaLH = new LocalHandler(rc)

      //Prepare the lambda's signature
      val argLocal = lambdaLH.freshLocal(argId)
      val argDef = ParamDef(argType, argLocal)
      lambdaLH.add(argId, argDef)

      val rawEnv = lambdaLH.freshLocal(".raw.env")
      val envDef = ParamDef(RawEnvType, rawEnv)

      //Load captured variables from the environment into locals
      val typedEnv = lambdaLH.freshLocal(".env")
      val envType = EnvironmentType(freeTypes)
      val translateEnv = Bitcast(typedEnv, rawEnv, envType)

      val loadFromEnv = freeVariables.zipWithIndex.flatMap{
        case (freeVar, index) => {
          val capturedType = lh.getType(freeVar)
          val capturedLocal = lambdaLH.dot(typedEnv, s"at$index")
          val capturedLocalGep = lambdaLH.dot(capturedLocal, "gep")

          val loadCapturedLocal = List(
            GepToIdx(capturedLocalGep, envType, Value(typedEnv), Some(index)),
            Load(capturedLocal, capturedType, capturedLocalGep))

          lambdaLH.add(freeVar, ParamDef(capturedType, capturedLocal))

          loadCapturedLocal
        }
      }

      val prepCaptured = if(freeVariables.isEmpty) Nil else translateEnv +: loadFromEnv

      //Make recursive call possible through a local
      val recursive = lambdaLH.dot(newLambdaId, "recursive")

      val recursiveEnv = if(freeVariables.isEmpty) {
        Value(NullLiteral)
      } else {
        Value(rawEnv)
      }

      val prepRecLambda = setLambda(recursive, lambdaGlobal, recursiveEnv, lambdaType)(lambdaLH)
      lambdaLH.add(newLambdaId, ParamDef(lambdaType, recursive))

      //Create top-level function for the lambda
      val emptyLambda = CreateLambda(retType, lambdaGlobal, List(argDef, envDef), recursive)
      globalHandler.addLambda(emptyLambda)

      val completeLambda = cgFunction(emptyLambda, lambdaLH, lambdaBody, globalHandler, prepRecLambda ++ prepCaptured)

      (lambdaGlobal, freeVariables, freeTypes)
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

    def getLambdaPrototype(tpe: Type) = tpe match {
      case LambdaType(argType, retType) => (argType, retType)
      case other => rc.reporter.fatalError(s"Type $tpe isn't a lambda")
    }

    def getLambdaFunction(lambda: Local, argType: Type, retType: Type)
      (implicit lh: LocalHandler): (Local, List[Instruction]) = {
        val funPtr = lh.dot(lambda, "function.gep")
        val fun = lh.dot(lambda, "function")
        val loadFun = List(
          GepToIdx(funPtr, LambdaType(argType, retType), Value(lambda), Some(0)),
          Load(fun, FunctionType(argType, retType), funPtr)
        )
        (fun, loadFun)
    }

    def getLambdaEnv(lambda: Local, argType: Type, retType: Type)(implicit lh: LocalHandler): (Local, List[Instruction]) = {
      val envPtr = lh.dot(lambda, "env.gep")
      val env = lh.dot(lambda, "env")
      val loadEnv = List(
        GepToIdx(envPtr, LambdaType(argType, retType), Value(lambda), Some(1)),
        Load(env, RawEnvType, envPtr)
      )
      (env, loadEnv)
    }

    def setLambda(lambda: Local, funGlobal: Global, env: Value, lambdaType: Type)(implicit lh: LocalHandler) = {
      val (argType, retType) = getLambdaPrototype(lambdaType)

      val allocation = List(allocate(lambda, lambdaType))
      val storeFun = setLambdaFunction(lambda, Value(funGlobal), argType, retType)
      val storeEnv = setLambdaEnv(lambda, env, argType, retType)

      allocation ++ storeFun ++ storeEnv
    }

    def setLambdaFunction(lambdaToSet: Local, function: Value, argType: Type, retType: Type)
      (implicit lh: LocalHandler): List[Instruction] = {
        val funPtr = lh.dot(lambdaToSet, "function.gep")
        val storeFun = List(
          GepToIdx(funPtr, LambdaType(argType, retType), Value(lambdaToSet), Some(0)),
          Store(function, FunctionType(argType, retType), funPtr)
        )
        storeFun
    }

    def setLambdaEnv(lambdaToSet: Local, env: Value, argType: Type, retType: Type)
      (implicit lh: LocalHandler): List[Instruction] = {
        val envPtr = lh.dot(lambdaToSet, "env.gep")
        val storeEnv = List(
          GepToIdx(envPtr, LambdaType(argType, retType), Value(lambdaToSet), Some(1)),
          Store(env, RawEnvType, envPtr)
        )
        storeEnv
    }

    def allocate(local: Local, tpe: Type)(implicit lh: LocalHandler): Instruction = {
      Malloc(local, lh.dot(local, "malloc"), tpe)
    }

    def preAllocate(local: Local, tpe: Type)(implicit lh: LocalHandler): List[Instruction] = tpe match {
      case EitherType(_, _) => List(allocate(local, tpe))
      case _ => Nil
    }

    def prepEnvironment(freeVariables: List[Identifier], freeTypes: List[Type], assign: Local)
      (implicit lh: LocalHandler): (List[Instruction], Value) = {

      val envType = EnvironmentType(freeTypes)

      if(freeVariables.isEmpty){
        (Nil, Value(NullLiteral))
      } else {
        //Create enviroment
        val env = lh.dot(assign, "env")
        val rawEnv = lh.dot(env, "malloc")
        val mallocEnv = Malloc(env, rawEnv, envType)

        //Store free variables into the environment
        val storeIntoEnv = freeVariables.zipWithIndex.flatMap{
          case (freeVar, index) => {
            val freeType = lh.getType(freeVar)
            val freeLocal = lh.getLocal(freeVar)
            val capturedLocalGep = lh.dot(env, s"at$index.gep")

            List(
              GepToIdx(capturedLocalGep, envType, Value(env), Some(index)),
              Store(Value(freeLocal), freeType, capturedLocalGep)
            )
          }
        }

        (mallocEnv +: storeIntoEnv, Value(rawEnv))
      }
    }

    def filterErasable(t: Tree): Tree = {
      Tree.traverse(t, _ => (), findErasable)
      t
    }

    def findErasable(t:Tree): Unit = t match {
      case
        MacroTypeDecl(_, _) |
        MacroTypeInst(_, _) |
        ErasableApp(_, _) |
        Refl(_, _) |
        Fold(_, _) |
        Unfold(_, _) |
        UnfoldPositive(_, _) |
        DefFunction(_, _, _, _, _, _) |
        ErasableLambda(_, _) |
        Abs(_) |
        TypeApp(_, _) |
        Because(_, _) => rc.reporter.fatalError(s"This tree should have been erased: $t")

      case _ => ()
    }
    def defaultValue(tpe: Type): Value = tpe match {
      case BooleanType | IRUnitType => Value(IRBooleanLiteral(false))
      case IRNatType => Value(Nat(BigInt(0)))
      case PairType(_, _) => ???
      case FirstType(pairType) => pairType match {
        case PairType(firstType, _) => defaultValue(firstType)
        case other => rc.reporter.fatalError(s"Expected a pair type but got $other")
      }
      case SecondType(pairType) => pairType match {
        case PairType(_, secondType) => defaultValue(secondType)
        case other => rc.reporter.fatalError(s"Expected a pair type but got $other")
      }
      case LeftType(inner) => defaultValue(inner)
      case RightType(inner) => defaultValue(inner)
      case other => rc.reporter.fatalError(s"There is no default value for type $other")
    }

    def assignee(toAssign: Option[Local])(implicit lh: LocalHandler) = toAssign getOrElse lh.freshLocal()
    def jumpTo(next: Option[Label]) = next.toList.map(label => Jump(label))

    def codegen(inputTree: Tree, block: Block, next: Option[Label], toAssign: Option[Local], resultType: Type)
      (implicit lh: LocalHandler, f: Function, globalHandler: GlobalHandler): (Block, List[Instruction]) =

      inputTree match {

        case value if isValue(value) => (block <:> cgValue(resultType, translateValue(value, resultType), next, toAssign), Nil)

        case Error(msg, _) => {
          if(msg.size < 256){
            val assign = resultType match {
              case EitherType(_, _) => Nil
              case other => List(Assign(assignee(toAssign), other, defaultValue(other)))
            }
            (block <:> assign <:> PrintError(msg, lh.freshLocal(".err")) <:> Exit <:> jumpTo(next), Nil)
          } else {
            rc.reporter.fatalError(s"Error message has ${msg.size} characters, maximum is 255")
          }
        }
        case call @ App(recApp, arg) => {

          val (id, flatArgs) = flattenApp(call)
          val result = assignee(toAssign)

          val (argType, retType) = getLambdaPrototype(lh.getType(id))
          val lambdaCall = cgLambdaCall(lh.getLocal(id), flatArgs, block, next, result, argType, retType)
          (lambdaCall, Nil)
        }

        case Pair(first, second) => {
          val pair = assignee(toAssign)
          val firstLocal = lh.dot(pair, "first")
          val secondLocal = lh.dot(pair, "second")

          val (firstType, secondType) = resultType match {
            case PairType(f, s) => (f, s)
            case other => rc.reporter.fatalError(s"Expected type is $resultType but value has type Pair(_, _)")
          }
          val pairType = PairType(firstType, secondType)

          val malloc = allocate(pair, pairType)

          val (firstBlock, firstPhi) = codegen(first, block <:> malloc, None, Some(firstLocal), firstType)
          val (secondBlock, secondPhi) = codegen(second, firstBlock <:> firstPhi, None, Some(secondLocal), secondType)

          val (firstPtr, secondPtr) = (lh.dot(pair, "first.gep"), lh.dot(pair, "second.gep"))

          val initialise = List(
            GepToIdx(firstPtr, pairType, Value(pair), Some(0)),
            Store(Value(firstLocal), firstType, firstPtr),
            GepToIdx(secondPtr, pairType, Value(pair), Some(1)),
            Store(Value(secondLocal), secondType, secondPtr)
          )

          (secondBlock <:> secondPhi <:> initialise <:> jumpTo(next), Nil)
        }

        case First(pair) => {
          val pairLocal = lh.freshLocal("pair")
          val pairType = typeOf(pair)(lh, globalHandler, Map.empty)
          val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal), pairType)

          val assignLocal = assignee(toAssign)
          val firstPtr = lh.dot(assignLocal, "first.gep")

          val prep = List(
            GepToIdx(firstPtr, pairType, Value(pairLocal), Some(0)),
            Load(assignLocal, resultType, firstPtr)
          )

          (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
        }

        case Second(pair) => {

          val pairLocal = lh.freshLocal("pair")
          val pairType = typeOf(pair)(lh, globalHandler, Map.empty)
          val (currentBlock, phi) = codegen(pair, block, None, Some(pairLocal), pairType)

          val assignLocal = assignee(toAssign)

          val secondPtr = lh.dot(pairLocal, "second.gep")

          val prep = List(
            GepToIdx(secondPtr, pairType, Value(pairLocal), Some(1)),
            Load(assignLocal, resultType, secondPtr)
          )

          (currentBlock <:> phi <:> prep <:> jumpTo(next), Nil)
        }

        case LetIn(optTpe, valueBody, Bind(newVar, rest)) => {
            val local = lh.freshLocal(newVar)
            val valueTpe = optTpe match {
              case Some(tpe) => translateType(tpe)
              case None => typeOf(valueBody)(lh, globalHandler, Map.empty)
            }

            val allocate = preAllocate(local, valueTpe)


            globalHandler.nameLambdasAfter(newVar)
            val (tempBlock, phi) = codegen(valueBody, block <:> allocate, None, Some(local), valueTpe)
            globalHandler.stopNamingAfter(newVar)

            lh.add(newVar, ParamDef(valueTpe, local))
            codegen(rest, tempBlock <:> phi, next, toAssign, resultType)
        }

        case Lambda(opt, Bind(argId, body)) => {

          val assign = assignee(toAssign)

          val (lambdaGlobal, freeVariables, freeTypes) = cgLambda(body, argId, resultType)
          val (prepEnv, envToPass) = prepEnvironment(freeVariables, freeTypes, assign)
          val makeLambda = setLambda(assign, lambdaGlobal, envToPass, resultType)

          (block <:> prepEnv <:> makeLambda <:> jumpTo(next), Nil)
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
              val argType = typeOfOperand(op)
              val (nextBlock, phi) = codegen(arg, currentBlock, None, Some(temp), argType)
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
          val scrutType = typeOf(scrut)(lh, globalHandler, Map.empty)
          val (currentBlock, scrutPhi) = codegen(scrut, block, None, Some(scrutLocal), scrutType)

          scrutType match {
            case LeftType(innerType) => {
              lh.add(varLeft, ParamDef(innerType, scrutLocal))
              /**
              * Only generate code for the left case since:
              * 1: We know it will be taken
              * 2: The type of the Right bind isn't known
              */
              codegen(bodyLeft, currentBlock <:> scrutPhi, next, toAssign, resultType)
            }

            case RightType(innerType) => {
              lh.add(varRight, ParamDef(innerType, scrutLocal))
              codegen(bodyRight, currentBlock <:> scrutPhi, next, toAssign, resultType)
            }

            case tpe @ EitherType(leftType, rightType) => {
              val leftLabel = lh.dot(block.label, "match.left")
              val rightLabel = lh.dot(block.label, "match.right")
              val afterLabel = lh.dot(block.label, "match.after")

              //Prevent identical Identifiers from shadowing eachother
              val freshVarLeft = Identifier.fresh(varLeft.name)
              val freshVarRight = Identifier.fresh(varRight.name)

              val freshBodyLeft = bodyLeft.replace(varLeft, freshVarLeft)(rc)
              val freshBodyRight = bodyRight.replace(varRight, freshVarRight)(rc)

              val (leftLocal, prepLeft) = getLeft(scrutLocal, tpe)
              val (rightLocal, prepRight) = getRight(scrutLocal, tpe)

              lh.add(freshVarLeft, ParamDef(leftType, leftLocal))
              lh.add(freshVarRight, ParamDef(rightType, rightLocal))

              val choose = cgEitherChoose(scrutLocal, tpe, leftLabel, rightLabel)
              f.add(currentBlock <:> scrutPhi <:> prepLeft <:> prepRight <:> choose)

              val afterPhi = cgAlternatives(leftLabel, freshBodyLeft, rightLabel, freshBodyRight, afterLabel, toAssign, resultType)

              (lh.newBlock(afterLabel) <:> afterPhi <:> jumpTo(next), Nil)
            }
          }
        }

        case LeftTree(either) => {

          val assignLocal = assignee(toAssign)

          val (currentBlock, phi) = (toAssign, resultType) match {
            case (Some(local), EitherType(leftType, _)) => {
              val leftLocal = lh.freshLocal("left")

              val eitherValuePtr = lh.dot(assignLocal, "left.value.gep")
              val eitherTypePtr = lh.dot(assignLocal, "left.type.gep")

              val assign = List(
                GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                Store(Value(IRBooleanLiteral(false)), BooleanType, eitherTypePtr),
                GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(1)),
                Store(Value(leftLocal), leftType, eitherValuePtr))

              val (prepBlock, p) = codegen(either, block, None, Some(leftLocal), leftType)
              (prepBlock <:> p <:> assign, Nil)
            }

            case (Some(local), LeftType(innerType)) => codegen(either, block, None, Some(local), innerType)
            case (Some(local), other) => rc.reporter.fatalError(s"Found LeftTree but expected $other when assigning $local")
            case (None, _) => (block, Nil)
          }

          (currentBlock <:> phi <:> jumpTo(next), Nil)
        }

        case RightTree(either) => {

          val assignLocal = assignee(toAssign)

          val (currentBlock, phi) = (toAssign, resultType) match {
            case (Some(local), EitherType(_, rightType)) => {
              val rightLocal = lh.freshLocal("right")

              val eitherValuePtr = lh.dot(assignLocal, "right.value.gep")
              val eitherTypePtr = lh.dot(assignLocal, "right.type.gep")

              val assign = List(
                GepToIdx(eitherTypePtr, resultType, Value(assignLocal), Some(0)),
                Store(Value(IRBooleanLiteral(true)), BooleanType, eitherTypePtr),
                GepToIdx(eitherValuePtr, resultType, Value(assignLocal), Some(2)),
                Store(Value(rightLocal), rightType, eitherValuePtr))

              val (prepBlock, p) = codegen(either, block, None, Some(rightLocal), rightType)
              (prepBlock <:> p <:> assign, Nil)
            }

            case (Some(local), RightType(innerType)) => codegen(either, block, None, Some(local), innerType)
            case (Some(local), other) => rc.reporter.fatalError(s"Found RightTree but expected $other when assigning $local")
            case (None, _) => (block, Nil)
          }

          (currentBlock <:> phi <:> jumpTo(next), Nil)
        }
        case _ => rc.reporter.fatalError(s"codegen not implemented for $inputTree")
    }
}
