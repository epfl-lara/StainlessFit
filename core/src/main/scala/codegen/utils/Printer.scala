package stainlessfit
package core
package codegen.utils

import core.util.RunContext
import core.Core._
import core.codegen.utils.Env
import core.codegen.llvm.Module
import scala.sys.process._
import java.io._


object Printer {

  def run(rc: RunContext, enableOutput: Boolean)(module : Module): Either[String, String] = {
    val outDirName = "LLVM_out"
    val filename = module.name.substring(0, module.name.lastIndexOf("."))

    def outputWithExt(ext: String) = s"$outDirName/$filename.$ext"

    def output(suffix: String, ext: String) = s"$outDirName/${filename}_$suffix.$ext"

    val (clang, opt) = {
      import Env._
      os match {
        case Linux   => ("clang", "opt")
        case Windows => ("clang.exe", "opt.exe")
        case Mac     => ("clang", "opt")
      }
    }

    val genOutput = output("gen", "ll")

    val passname = rc.config.llvmPassName
    val optiOutput = output(passname, "ll")
    val compiled = output(passname, "out")

    val optOptions = s"-S $genOutput -$passname -o $optiOutput"
    val clangOptions = s"$optiOutput -o $compiled"

    def printErrOutput(errOutput: String) = {
      if(errOutput.contains("error")){
        rc.reporter.fatalError(errOutput)
      } else if(enableOutput && errOutput.contains("warning")){
        rc.reporter.warning(errOutput)
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
          val (exitValue, standardOutput, errOutput) = Core.runCommand(exec)
          printErrOutput(errOutput)

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

    Right(s"./$compiled")
  }
}
