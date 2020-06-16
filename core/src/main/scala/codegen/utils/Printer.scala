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

    val clang = {
      import Env._
      os match {
        case Linux   => "clang"
        case Windows => "clang.exe"
        case Mac     => "clang"
      }
    }

    val genOutput = output("gen", "ll")
    val passname = rc.config.llvmPassName
    val compiled = output(passname, "out")

    val clangOptions = s"$genOutput -$passname -o $compiled"

    def printErrOutput(errOutput: String) = {
      if(errOutput.contains("error")){
        rc.reporter.fatalError(errOutput)
      } else if(enableOutput && errOutput.contains("warning")){
        rc.reporter.warning(errOutput)
      }
    }

    val outDir = new File(outDirName)
    if (!outDir.exists()) {
      outDir.mkdir()
    }

    module.printToFile(genOutput)(rc)

    val exec = s"$clang $clangOptions"

    try {
        val (exitValue, standardOutput, errOutput) = Core.runCommand(exec)
        printErrOutput(errOutput)

      } catch {
        case _: IOException =>
          rc.reporter.fatalError(
                s"clang utility was not found under system path, " +
                "or did not have permission to execute"
          )
        case _: RuntimeException =>
          rc.reporter.fatalError(s"clang failed to compile text file $genOutput to binary")
      }

    Right(s"./$compiled")
  }
}
