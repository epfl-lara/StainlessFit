package stainlessfit
package cli

import core._

import buildinfo.BuildInfo
import scopt.OParser
import java.io.File

object ConfigParser {

  def parse(args: Seq[String]): Option[Config] =
    OParser.parse(options, args, Config())

  private implicit val scoptRead: scopt.Read[DebugSection] =
    scopt.Read.reads(DebugSection(_))

  private val builder = OParser.builder[Config]

  private val options = {
    import builder._

    OParser.sequence(
      programName("stainless-fit"),
      head("StainlessFit", BuildInfo.version),
      help("help").text("Prints help information"),
      opt[Seq[DebugSection]]("debug")
        .action((ds, c) => c.copy(debugSections = ds.toSet))
        .text(s"Enable debugging information (available: ${DebugSection.available.mkString(", ")})"),
      opt[Unit]("html")
        .action((_, c) => c.copy(html = true))
        .text("Enable HTML output with typing derivation"),
      opt[Int]("refresh")
        .action((n, c) => c.copy(refresh = n))
        .text("Have the HTML file automatically refresh every <value> seconds"),
      opt[Unit]("bench")
        .action((_, c) => c.copy(bench = true))
        .text("Display benchmarked times"),
      opt[Unit]("watch")
        .action((_, c) => c.copy(watch = true))
        .text("Re-run on file modification"),
      opt[Unit]("no-colors")
        .action((_, c) => c.copy(colors = false))
        .text("Disable colors in output"),
      opt[Unit]("no-info")
        .action((_, c) => c.copy(info = false))
        .text("Disable [INFO] prefix in output"),
      opt[Unit]("print-ids")
        .action((_, c) => c.copy(printUniqueIds = true))
        .text("Print unique identifiers"),
      opt[Unit]("O1")
        .action((_, c) => c.copy(llvmPassName = "O1")),
      opt[Unit]("O2")
        .action((_, c) => c.copy(llvmPassName = "O2")),
      opt[Unit]("O3")
        .action((_, c) => c.copy(llvmPassName = "O3")),

      note(""),
      cmd("eval")
        .action((_, c) => c.copy(mode = Mode.Eval))
        .text("Evaluate the given file")
        .children(
          arg[File]("<file>")
            .required()
            .action((f, c) => c.copy(file = f))
            .text("The file to evaluate, in `sf` format")
        ),

      note(""),
      cmd("typecheck")
        .action((_, c) => c.copy(mode = Mode.TypeCheck))
        .text("Typecheck the given file")
        .children(
          arg[File]("<file>")
            .required()
            .action((f, c) => c.copy(file = f))
            .text("The file to typecheck, in `sf` format")
        ),

      note(""),
      cmd("compile")
        .action((_, c) => c.copy(mode = Mode.Compile))
        .text("Compile the given file")
        .children(
          arg[File]("<file>")
            .required()
            .action((f, c) => c.copy(file = f))
            .text("The file to compile, in `sf` format")
        ),
      note(""),
      cmd("execute")
        .action((_, c) => c.copy(mode = Mode.Execute))
        .text("Compile and execute the given file")
        .children(
          arg[File]("<file>")
            .required()
            .action((f, c) => c.copy(file = f))
            .text("The file to execute, in `sf` format")
        ),

      checkConfig {
        case c if c.mode == null => failure("Please specify a command: eval, typecheck, compile")
        case c if c.file != null && !c.file.exists => failure(s"File not found: ${c.file}")
        case c =>
          c.debugSections.find(!DebugSection.available(_)) match {
            case None => success
            case Some(section) => failure(s"$section is not a valid debug section")
          }
      }
    )
  }

}
