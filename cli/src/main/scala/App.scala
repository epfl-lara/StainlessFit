import trees._
import interpreter._
import typechecker._
import typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object App {
  def launch(config: Config): Unit = {
    config.mode match {
      case Mode.Eval => eval(config)
      case Mode.TypeCheck => typeCheck(config)
    }
  }

  val eval = watchable { config =>
    Core.evalFile(config.file) match {
      case Left(error) =>
        System.err.println(s"[ERROR] Error during evaluation: $error")
        false
      case Right(value) =>
        System.out.println(s"$value")
        true
    }
  }

  val typeCheck = watchable { config =>
    val file = config.file
    Core.typeCheckFile(file) match {
      case Left(error) =>
        System.err.println(s"[ERROR] $error")
        false

      case Right((success, _)) if success =>
        System.out.println(s"Type checked file $file successfully.")
        true

      case _ =>
        System.err.println(s"[ERROR] Error while type checking file $file.")
        false
    }
  }

  def watchable(action: Config => Boolean): Config => Unit = (c: Config) =>
    if (c.watch) {
      watchFile(c.file)(action(c))
    }
    else {
      val result = action(c)
      if (!result) System.exit(1)
    }

  def watchFile(file: File)(action: => Unit): Unit = {
    val watcher = new util.FileWatcher(
      scala.collection.immutable.Set(file.getAbsoluteFile),
      () =>
        try {
          action
        } catch {
          case e: Throwable =>
            println("[ERROR] An exception was thrown:")
            e.printStackTrace()
        }
    )

    watcher.run()
  }
}

