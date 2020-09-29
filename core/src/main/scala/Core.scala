/* Copyright 2019-2020 EPFL, Lausanne */

package stainlessfit
package core

import core.trees._
import core.interpreter._
import core.typechecker._
import core.typechecker.Derivation._

import core.codegen._
import core.codegen.utils.{Printer => LLVMPrinter}

import parser.FitParser
import parser.FitLexer

import extraction._

import java.io.{File, ByteArrayOutputStream, PrintWriter}
import scala.sys.process._

import core.util.RunContext

import scala.sys.process._

object Core {

  def parseString(s: String)(implicit rc: RunContext): Either[String, Tree] = {
    val it = s.iterator

    rc.parser(FitLexer(it)) match {
      case rc.parser.LL1.Parsed(value, _) =>
        Right(value)
      case rc.parser.LL1.UnexpectedEnd(rest) =>
        Left(
          s"""|Error during parsing, unexpected end of input.
              |Expected token: ${rest.first.mkString("   ")}""".stripMargin
        )
      case rc.parser.LL1.UnexpectedToken(t, rest) =>
        Left(
          s"""|Error during parsing, unexpected token at position ${t.pos}: $t
              |Expected token: ${rest.first.mkString("   ")}""".stripMargin
        )
    }
  }

  def parseFile(f: File)(implicit rc: RunContext): Either[String, Tree] = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val regex = """Include\("(.*)"\)""".r
    val completeString = regex.replaceAllIn(s, m =>
      scala.io.Source.fromFile(new File(f.getAbsoluteFile().getParentFile().getCanonicalPath(), m.group(1))).getLines.mkString("\n") + "\n"
    )
    rc.bench.time("Scallion parsing") { parseString(completeString) }
  }

  def evalFile(f: File)(implicit rc: RunContext): Either[String, Tree] =
    parseFile(f) flatMap { src =>

      val pipeline =
        DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
        DebugPhase(new Namer(), "Namer") andThen
        DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
        DebugPhase(new Erasure(), "Erasure")

      val (t, _) = pipeline.transform(src)

      rc.bench.time("evaluation"){Interpreter.evaluate(t)} match {
        case Error(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def hasZ3(): Boolean = {
    try {
      "z3 --version".!(ProcessLogger(_ => ()))
      true
    } catch {
      case _: Throwable => false
    }
  }

  def typeCheckFile(f: File)(implicit rc: RunContext): Either[String, (Boolean, NodeTree[Judgment])] = {
    if (hasZ3()) {
      parseFile(f) flatMap { src =>

        val pipeline =
          DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
          DebugPhase(new FixIndexing(), "FixIndexing") andThen
          DebugPhase(new Namer(), "Namer") andThen
          DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers")

        val (t, _) = pipeline.transform(src)

        rc.bench.time("Type Checking") { new TypeChecker().infer(t) } match {
          case None => Left(s"Could not typecheck: $f")
          case Some((success, tree)) =>
            if (rc.config.html)
              rc.bench.time("makeHTMLFile") {
                util.HTMLOutput.makeHTMLFile(f, List(tree), success)
              }

            Right((success, tree))
        }
      }
    } else {
      Left("The z3 solver is required for the typecheck command")
    }
  }

  def sDepFile(f: File)(implicit rc: RunContext): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(f) flatMap { src =>

      val pipeline =
        DebugPhase(new DefFunctionElimination(), "DefFunctionElimination") andThen
        DebugPhase(new FixIndexing(), "FixIndexing") andThen
        DebugPhase(new Namer(), "Namer") andThen
        DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
        DebugPhase(new ChooseEncoding(), "ChooseEncoding")

      val (t, _) = pipeline.transform(src)

      rc.bench.time("SDep") { new SDep().infer(t) } match {
        case None => Left(s"Could not typecheck: $f")
        case Some((success, tree)) =>
          if (rc.config.html)
            rc.bench.time("makeHTMLFile") {
              util.HTMLOutput.makeHTMLFile(f, List(tree), success)
            }

          Right((success, tree))
      }
    }
  }

  def compileFile(f: File, enableOutput: Boolean = true)(implicit rc: RunContext): Either[String, String] = {

    parseFile(f) flatMap { src =>

      val pipeline =
        DebugPhase(new DefFunctionLLVMConversion(), "DefFunctionLLVMConversion") andThen
        DebugPhase(new BuiltInIdentifiers(), "BuiltInIdentifiers") andThen
        DebugPhase(new PartialErasure(), "PartialErasure")

      val (t, _) = pipeline.transform(src)

      rc.bench.time("Code generation") {
        val module = new CodeGen(rc).genLLVM(t, true, f.getName)
        LLVMPrinter.run(rc, enableOutput)(module)
      }
    }
  }

  def runCommand(cmd: String): (Int, String, String) = {
    val stdoutStream = new ByteArrayOutputStream
    val stderrStream = new ByteArrayOutputStream
    val stdoutWriter = new PrintWriter(stdoutStream)
    val stderrWriter = new PrintWriter(stderrStream)
    val exitValue = cmd.!(ProcessLogger(stdoutWriter.println, stderrWriter.println))
    stdoutWriter.close()
    stderrWriter.close()
    (exitValue, stdoutStream.toString, stderrStream.toString)
  }

  def executeFile(f: File, enableOutput: Boolean = true)(implicit rc: RunContext): Either[String, String] = {
    def printResult(result: String): Unit = {
      if(enableOutput && !result.isEmpty){
        rc.reporter.info(result)
      }
    }

    def printWarnings(errOutput: String): Unit = {
      if(errOutput.contains("warning")){
        rc.reporter.warning(errOutput)
      }
    }

    compileFile(f, enableOutput) match {
      case Left(error) => Left(error)
      case Right(command) => {
        try {
          val (exitValue, standardOutput, errOutput) = rc.bench.time("Execution: " + rc.config.llvmPassName){
            runCommand(command)
          }
          val result = standardOutput.dropRight(1)

          if(errOutput.contains("error")){
            Left(errOutput)
          } else {
            printWarnings(errOutput)

            if(exitValue != 0){
              Left(result)
            } else {
              printResult(result)
              Right(result)
            }
          }

        } catch {
          case _: RuntimeException =>
          Left(s"Could not run the file: $command. Check permissions")
        }
      }
    }
  }

  def evalFile(s: String)(implicit rc: RunContext): Either[String, Tree] =
    evalFile(new File(s))

  def typeCheckFile(s: String)(implicit rc: RunContext): Either[String, (Boolean, NodeTree[Judgment])] =
    typeCheckFile(new File(s))

  def compileFile(s: String)(implicit rc: RunContext): Either[String, String] =
    compileFile(new File(s))

  def executeFile(s: String, enableOutput: Boolean)(implicit rc: RunContext): Either[String, String] =
    executeFile(new File(s), enableOutput)
}
