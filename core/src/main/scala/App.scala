/* Copyright 2019-2020 EPFL, Lausanne */

/* Copyright 2019-2020 EPFL IC LARA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package stainlessfit
package core

import java.io.File

import core.Core

import util.Bench
import util.FileWatcher
import util.Reporter
import util.RunContext
import parser.FitParser
import trees.Printer

class App()(implicit rc: RunContext) {

  val file = rc.config.file

  def start(): Unit = {
    rc.config.mode match {
      case Mode.Eval      => eval()
      case Mode.TypeCheck => typeCheck()
      case Mode.SDep  => sDep()
      case Mode.Compile   => compile()
      case Mode.Execute   => execute()
    }
  }

  def eval(): Unit = FileWatcher.watchable(file) {
    Core.evalFile(file) match {
      case Left(error) =>
        rc.reporter.error(s"Error during evaluation: $error")
        false
      case Right(value) =>
        Printer.exprInfo(value)
        true
    }
  }

  def typeCheck(): Unit = FileWatcher.watchable(file) {
    Core.typeCheckFile(file) match {
      case Left(error) =>
        rc.reporter.error(s"$error")
        false

      case Right((success, _)) if success =>
        rc.reporter.info(s"Successfully typechecked file '$file'.")
        true

      case _ =>
        rc.reporter.error(s"There was an error while typechecking file '$file'.")
        false
    }
  }

  def sDep(): Unit = FileWatcher.watchable(file) {
    Core.sDepFile(file) match {
      case Left(error) =>
        rc.reporter.error(s"$error")
        false

      case Right((success, _)) if success =>
        rc.reporter.info(s"Successfully typechecked file '$file'.")
        true

      case _ =>
        rc.reporter.error(s"There was an error while typechecking file '$file'.")
        false
    }
  }

  def compile(): Unit = FileWatcher.watchable(file) {
    Core.compileFile(file) match {
      case Left(error) =>
        rc.reporter.error(s"Error during compilation: $error")
        false
      case Right(value) =>
        rc.reporter.info(s"Successfully compiled file '$file'.")
        true
    }
  }

  def execute(): Unit = FileWatcher.watchable(file) {
    Core.executeFile(file) match {
      case Left(error) =>
        rc.reporter.error(s"Error during execution: $error")
        false
      case Right(value) =>
        true
    }
  }
}

object App {
  def launch(config: Config): Unit = {

    implicit val rc = new RunContext(config)

    val app = new App()

    app.start()

    rc.bench.stop()

    if (config.bench)
      rc.bench.report(rc.reporter)
  }
}
