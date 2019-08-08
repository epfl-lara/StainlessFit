ThisBuild / scalaVersion := "2.12.8"

ThisBuild / resolvers ++= Seq(
    Resolver.bintrayRepo("epfl-lara", "maven")
)

/* Using unmanaged ScalaZ3 as in Inox */

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"

core / libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.0.8" % "test",
  "ch.epfl.lara" %% "scallion" % "0.1"
)

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainlesscore",
    assemblyJarName in assembly := "stainless-core.jar",
    test in assembly := {}
  )
  .dependsOn(verified)

lazy val verified = project
  .in(file("verified"))
  // .enablePlugins(StainlessPlugin)
  .settings(
    name := "stainlesscore-verified",
    Compile / unmanagedJars += {
      baseDirectory.value / "unmanaged" / "scalaz3-unix-64-2.12.jar"
    }
  )
