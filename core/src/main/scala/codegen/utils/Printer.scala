package stainlessfit
package core
package codegen.utils

import core.util.RunContext
import core.codegen.utils.Env
import core.codegen.llvm.Module
import scala.sys.process._
import java.io._


object Printer {

  def run(rc: RunContext, printInfo: Boolean)(module : Module): Either[String, String] = {
    val outDirName = "LLVM_out"
    val filename = module.name.substring(0, module.name.lastIndexOf("."))

    def outputWithExt(ext: String) = s"$outDirName/$filename.$ext"

    def output(suffix: String, ext: String) = s"$outDirName/${filename}_$suffix.$ext"

    //TODO require the end-user to have each command in their path
    val (clang, opt) = {
      import Env._
      os match {
        case Linux   => ("clang", "opt")
        case Windows => rc.reporter.fatalError("Windows compilation not et implemented")
        case Mac     => ("clang", "/usr/local/opt/llvm/bin/opt")
      }
    }

    val genOutput = output("gen", "ll")

    val passname = "O1"
    val optiOutput = output(passname, "ll")
    val compiled = output(passname, "out")

    val optOptions = s"-S $genOutput -$passname -o $optiOutput"
    val clangOptions = s"$optiOutput -o $compiled"

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

    def reporterSelect(output: String) = {
        if(output.contains("error")){
          rc.reporter.fatalError(output)
        }

        if(printInfo && output.contains("warning")){
          rc.reporter.warning(output)
        } else if(printInfo && output.size != 0){
          rc.reporter.info(output)
        }
      }


    def llvm(action: String) = {
      val (exec, program, errorMsg) = if(action == "optimize"){
        (s"$opt $optOptions", opt, s"opt failed to optimise file $optiOutput")
      } else if(action == "compile"){
        (s"$clang $clangOptions", clang, s"clang failed to compile text file $optiOutput to binary")
      } else {
        rc.reporter.fatalError(s"Unknown action $action")
      }

      try {
          val (exitValue, standardOutput, errOutput) = runCommand(exec)
          reporterSelect(errOutput)

        } catch {
          case _: IOException =>
            rc.reporter.fatalError(
                  s"$program utility was not found under system path, " +
                  "or did not have permission to execute"
            )
          case _: RuntimeException =>
            rc.reporter.fatalError(errorMsg)
        }
    }

    val outDir = new File(outDirName)
    if (!outDir.exists()) {
      outDir.mkdir()
    }

    module.printToFile(genOutput)(rc)

    llvm("optimize")

    llvm("compile")

    try {
      val (exitValue, standardOutput, errOutput) = rc.bench.time("Execution"){ runCommand(s"./$compiled") }
      reporterSelect(standardOutput)
      reporterSelect(errOutput)
      Right(standardOutput)
    } catch {
      case _: RuntimeException =>
      rc.reporter.fatalError(s"Could not run the file: $compiled. Check permissions")
      Left("")
    }
  }
}
