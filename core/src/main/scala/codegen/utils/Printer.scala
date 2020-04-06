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
          case Mac     => ("clang", "opt")
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
          exec.!!
        } catch {
          case _: IOException =>
            rc.reporter.fatalError(
                  s"opt utility was not found under system path, " +
                  "or did not have permission to execute"
            )
          case _: RuntimeException =>
            rc.reporter.fatalError(errorMsg)
        }
    }

    llvm("optimize")

    llvm("compile")

    // try {
    //     s"$opt $optOptions".!!
    //   } catch {
    //     case _: IOException =>
    //       rc.reporter.fatalError(
    //             s"opt utility was not found under system path, " +
    //             "or did not have permission to execute"
    //       )
    //     case _: RuntimeException =>
    //       rc.reporter.fatalError(s"opt failed to optimise file $optiOutput")
    //   }
    //
    // try {
    //     s"$clang $clangOptions".!!
    //   } catch {
    //     case _: IOException =>
    //       rc.reporter.fatalError(
    //             s"clang utility was not found under system path, " +
    //             "or did not have permission to execute"
    //       )
    //     case _: RuntimeException =>
    //       rc.reporter.fatalError(s"clang failed to compile text file $optiOutput to binary")
    //   }

    try {
      val ret = (s"./$compiled").!
      println(s"[OUTPUT] $ret")
    } catch {
      case _: RuntimeException =>
      rc.reporter.warning(s"Could not run the file: $compiled. Check permissions")
    }
  }
}
