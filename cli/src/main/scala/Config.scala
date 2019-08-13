import buildinfo.BuildInfo
import scopt.OParser
import java.io.File

sealed abstract class Mode
object Mode {
  case object Eval      extends Mode
  case object TypeCheck extends Mode
}

case class Config(
  mode: Mode       = null,
  file: File       = null,
  watch: Boolean   = false,
  debug: Boolean   = false,
  verbose: Boolean = false,
)

object Config {

  def parse(args: Array[String]): Option[Config] =
    OParser.parse(options, args, Config())

  private val builder = OParser.builder[Config]
  private val options = {
    import builder._

    OParser.sequence(
      programName("stainless-core"),
      head("StainlessCore", BuildInfo.version),
      help("help").text("Prints help information"),
      opt[Unit]("verbose")
        .action((_, c) => c.copy(verbose = true))
        .text("Enable verbose output"),
      opt[Unit]("debug")
        .action((_, c) => c.copy(debug = true))
        .text("Enable debug output"),
      opt[Unit]("watch")
        .action((_, c) => c.copy(watch = true))
        .text("Re-run on file modification"),
      cmd("eval")
        .action((_, c) => c.copy(mode = Mode.Eval))
        .text("Evaluate the given file")
        .children(
          arg[File]("<file>...")
            .required()
            .action((f, c) => c.copy(file = f)),
        ),
      cmd("typecheck")
        .action((_, c) => c.copy(mode = Mode.TypeCheck))
        .text("Type check the given file")
        .children(
          arg[File]("<file>...")
            .required()
            .action((f, c) => c.copy(file = f)),
        ),
      checkConfig {
        case c if c.mode == null => failure("Please specify a command: eval, typecheck")
        case c if !c.file.exists => failure(s"File not found: ${c.file}")
        case _ => success
      }
    )
  }
}
