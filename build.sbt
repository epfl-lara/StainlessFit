ThisBuild / scalaVersion := "2.12.8"

ThisBuild / resolvers ++= Seq(
    Resolver.bintrayRepo("epfl-lara", "maven")
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
      (ThisBuild / baseDirectory).value / "unmanaged" / s"scalaz3-${OS.name}-${OS.arch}-${scalaBinaryVersion.value}.jar"
    }
  )
