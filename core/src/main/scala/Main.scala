import trees._
import interpreter._
import typechecker._
import typechecker.Derivation._

import parser.ScalaParser
import parser.ScalaLexer

import java.io.File

import stainless.collection._
import stainless.lang._

object Main {

  val assertFun = """def assert(b: {b: Bool, b}): Unit = { if(b) () else Error[Unit]("Assertion failed") }"""

  def parseFile(f: File): Either[String, Tree] = {
    val s = scala.io.Source.fromFile(f).getLines.mkString("\n")
    val it = (assertFun + s).toIterator
    ScalaParser.apply(ScalaLexer.apply(it)) match {
      case ScalaParser.Parsed(value, _) =>
        Right(value)
      case ScalaParser.UnexpectedEnd(_) =>
        Left("Error during parsing: unexpected end.")
      case ScalaParser.UnexpectedToken(t, _) =>
        Left("Error during parsing: unexpected token." + t)
    }
  }

  def evalFile(f: File): Either[String, Tree] =
    parseFile(f) flatMap { src =>
      val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)

      Interpreter.evaluate(t.erase(), 100000000) match {
        case ErrorTree(error, _) => Left(error)
        case v => Right(v)
      }
    }

  def typeCheckFile(f: File): Either[String, (Boolean, NodeTree[Judgment])] = {
    parseFile(f) flatMap { src =>
      val (t, _, max) = Tree.setId(src, stainless.lang.Map(), 0)
      TypeChecker.infer(t, max) match {
        case None() => Left(s"Could not type check: $f")
        case Some((success, tree)) =>
          Derivation.makeHTMLFile(
            f,
            List(tree),
            success
          )

          Right((success, tree))
      }
    }
  }

  def evalFile(s: String): Either[String, Tree] =
    evalFile(new File(s))

  def typeCheckFile(s: String): Either[String, (Boolean, NodeTree[Judgment])] =
    typeCheckFile(new File(s))


  object App {
    def launch(config: Config): Unit = {
      config.mode match {
        case Eval => eval(config)
        case TypeCheck => typeCheck(config)
      }
    }

    val eval = watchable { config =>
      evalFile(config.file) match {
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
      typeCheckFile(file) match {
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

  def main(args: Array[String]): Unit = {
    Config.parse(args).foreach(App.launch)
  }
}
