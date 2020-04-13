package stainlessfit
package core
package codegen.utils

import core.util.RunContext
import core.codegen.utils.Env
import core.codegen.llvm.Module
import scala.sys.process._
import java.io._


object Printer {

  def run(rc: RunContext)(module : Module) = {
      val outDirName = "LLVM_out"
      val filename = module.name.substring(0, module.name.lastIndexOf("."))

      def outputWithExt(ext: String) = s"$outDirName/$filename.$ext"

      val (clang, opt) = {
        import Env._
        os match {
          case Linux   => ("clang", "opt")
          case Windows => rc.reporter.fatalError("Windows compilation not et implemented")
          case Mac     => ("clang", "/usr/local/opt/llvm/bin/opt")
        }
    }

    def output(suffix: String, ext: String) = s"$outDirName/${filename}_$suffix.$ext"

    val genOutput = output("gen", "ll")

    val passname = "O1"
    val optiOutput = output(passname, "ll")
    val compiled = output(passname, "out")

    val optOptions = s"-S $genOutput -$passname -o $optiOutput"
    val clangOptions = s"$optiOutput -o $compiled"

    val outDir = new File(outDirName)
    if (!outDir.exists()) {
      outDir.mkdir()
    }

    //TODO get the current target triple here
    // try {
    //   val targetTriple = ("clang -print-effective-triple").!
    // }

    module.printToFile(genOutput)

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

    llvm("optimize")

    llvm("compile")

    try {
      val (exitValue, standardOutput, errOutput) = rc.bench.time("execution"){ runCommand(s"./$compiled") }
      rc.reporter.info(standardOutput)
      reporterSelect(errOutput)
    } catch {
      case _: RuntimeException =>
      rc.reporter.warning(s"Could not run the file: $compiled. Check permissions")
    }

    // try {
    //   // val format =
    //   //   "%U user\n" +
    //   //   "%S system\n" +
    //   //   "%e elapsed"
    //   // val (exitValue, standardOutput, errOutput) = runCommand(s"time -f '${format}' ./$compiled")
    //
    //   val (startValue, startStd, _) = runCommand(s"date +%s%N")
    //   val (exitValue, standardOutput, errOutput) = runCommand(s"time -p ./$compiled") //date +%s
    //   val (endValue, endStd, _) = runCommand(s"date +%s%N")
    //
    //   val time = (BigInt(endStd.trim) - BigInt(startStd.trim))/BigInt(1000000)
    //
    //   rc.reporter.info(standardOutput)
    //
    //   if(time <= BigInt(10)){
    //     rc.reporter.info(s"time <= 10 ms")
    //   } else {
    //     reporterSelect(errOutput)
    //   }
    // } catch {
    //   case _: RuntimeException =>
    //   rc.reporter.warning(s"Could not run the file: $compiled. Check permissions")
    // }

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

    def reporterSelect(output: String) =
      if(output.contains("warning")){
        rc.reporter.warning(output)
      } else if(output.contains("error")){
        rc.reporter.error(output)
      } else if(output.size != 0){
        rc.reporter.info(output)
      }
  }
}
