package cli

import java.io.File

import core.Reporter
import core.Core

class App(val config: Config, val reporter: Reporter) {

  def eval(file: File) = watchable(file) {
    Core.evalFile(config.file) match {
      case Left(error) =>
        reporter.error(s"Error during evaluation: $error")
        false
      case Right(value) =>
        reporter.info(s"$value")
        true
    }
  }

  def typeCheck(file: File) = watchable(file) {
    val file = config.file
    Core.typeCheckFile(file) match {
      case Left(error) =>
        reporter.error(s"$error")
        false

      case Right((success, _)) if success =>
        reporter.info(s"Successfully type checked file '$file'.")
        true

      case _ =>
        reporter.error(s"Error while type checking file '$file'.")
        false
    }
  }

  def watchable(file: File)(action: => Boolean): Unit = {
    if (config.watch) {
      watchFile(file)(action)
    }
    else {
      val result = action
      if (!result) System.exit(1)
    }
  }

  def watchFile(file: File)(action: => Unit): Unit = {
    val watcher = new util.FileWatcher(
      Set(file.getAbsoluteFile),
      () =>
        try {
          action
        } catch {
          case e: Throwable =>
            reporter.error("An exception was thrown:")
            reporter.error(e)
        }
    )

    watcher.run()
  }
}

object App {
  def launch(config: Config): Unit = {
    val reporter = new Reporter(config.colors)

    val app = new App(config, reporter)

    config.mode match {
      case Mode.Eval      => app.eval(config.file)
      case Mode.TypeCheck => app.typeCheck(config.file)
    }
  }
}
