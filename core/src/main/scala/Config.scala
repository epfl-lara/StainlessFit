package core

import buildinfo.BuildInfo
import scopt.OParser
import java.io.File

sealed abstract class Mode
object Mode {
  case object Eval      extends Mode
  case object TypeCheck extends Mode
}

case class Config(
  mode: Mode                       = null,
  file: File                       = null,
  watch: Boolean                   = false,
  html: Boolean                    = false,
  refresh: Int                     = 0,
  bench: Boolean                   = false,
  colors: Boolean                  = true,
  verbose: Boolean                 = false,
  debugSections: Set[DebugSection] = Set.empty,
)

object Config {

  def default = Config()

  def parse(args: Array[String]): Option[Config] =
    OParser.parse(options, args, Config())

  private val builder = OParser.builder[Config]
  private val options = {
    import builder._

    OParser.sequence(
      programName("stainless-fit"),
      head("StainlessFit", BuildInfo.version),
      help("help").text("Prints help information"),
      opt[Unit]("verbose")
        .action((_, c) => c.copy(verbose = true))
        .text("Enable verbose output"),
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

      checkConfig {
        case c if c.mode == null => failure("Please specify a command: eval, typecheck")
        case c if c.file != null && !c.file.exists => failure(s"File not found: ${c.file}")
        case _ => success
      }
    )
  }
}
