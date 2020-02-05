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

import core.util.Bench
import core.util.FileWatcher
import core.util.Reporter
import core.util.RunContext

class App(val rc: RunContext) {

  val file = rc.config.file

  def start(): Unit = {
    rc.config.mode match {
      case Mode.Eval      => eval()
      case Mode.TypeCheck => typeCheck()
    }
  }

  def eval(): Unit = FileWatcher.watchable(rc, file) {
    Core.evalFile(rc, file) match {
      case Left(error) =>
        rc.reporter.error(s"Error during evaluation: $error")
        false
      case Right(value) =>
        rc.reporter.info(s"$value")
        true
    }
  }

  def typeCheck(): Unit = FileWatcher.watchable(rc, file) {
    Core.typeCheckFile(rc, file, rc.config.html) match {
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
}

object App {
  def launch(config: Config): Unit = {

    val rc = new RunContext(config)
    val app = new App(rc)

    app.start()

    rc.bench.stop()

    if (config.bench)
      rc.bench.report(rc.reporter)
  }
}
