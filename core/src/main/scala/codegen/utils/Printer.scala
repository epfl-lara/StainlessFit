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

      val inPath = {
        import Env._
        os match {
          case Linux   => "clang"
          case Windows => rc.reporter.fatalError("Windows compilation not et implemented")
          case Mac     => "clang"
        }
    }

    val clangOptions = s"${outputWithExt("ll")} -o $outDirName/$filename.out"
    val optOptions = s"-S ${outputWithExt("ll")} -O1 -o $outDirName/${filename}Opti.ll"

    val outDir = new File(outDirName)
    if (!outDir.exists()) {
      outDir.mkdir()
    }

    module.printToFile(outputWithExt("ll"))

    try {
        s"$inPath $clangOptions".!!
        s"opt $optOptions".!! //TODO update opt command depending on OS
      } catch {
        case _: IOException =>
          rc.reporter.fatalError(
                s"clang utility was not found under system path, " +
                "or did not have permission to execute"
          )
        case _: RuntimeException =>
          rc.reporter.fatalError(s"clang failed to compile text file ${outputWithExt("ll")} to binary")
      }
  }
}
