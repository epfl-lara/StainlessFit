package stainlessfit
package core
package codegen

import trees._
import util.RunContext
import codegen.llvm.IR._

// General stuff
import org.bytedeco.javacpp._;

// Headers required by LLVM
import org.bytedeco.llvm.LLVM._;
import org.bytedeco.llvm.global.LLVM._;

object CodeGen {
    def genLLVM(tree: Tree, isMain: Boolean)(implicit rc: RunContext): Unit = {

        def cgTree(tree: Tree, resultId: Identifier): Code = tree match {

            case IfThenElse(cond, thenn, elze) => {
              val condBlock = Block(Identifier.fresh("cond"), Nil)
              val thennBlock = Block(Identifier.fresh("then"), Nil)
              val elzeBlock = Block(Identifier.fresh("else"), Nil)
              ???
            }
            case _ => rc.reporter.fatalError(s"Code generation not yet implemented for $tree")
        }

        val firstBlock = Block(Identifier.fresh("Entry"), Nil)
    }
}
