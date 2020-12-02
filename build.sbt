
enablePlugins(GitVersioning)
git.useGitDescribe := true

ThisBuild / organization := "ch.epfl.lara"
ThisBuild / scalaVersion := "2.13.3"

ThisBuild / resolvers ++= Seq(
  Resolver.bintrayRepo("epfl-lara", "maven")
)

ThisBuild / scalacOptions ++= Seq(
  "-encoding", "UTF-8",
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Wconf:cat=other-match-analysis&src=Trees.scala:s," +
    "cat=other-match-analysis&src=Printer.scala:s," +
    "cat=other-match-analysis&src=Parser.scala:s," +
    "msg=Exhaustivity analysis reached max recursion depth:s"
)

ThisBuild / maxErrors := 5

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainless-fit",
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.2" % "test",
      "ch.epfl.lara" %% "silex" % "0.5",
    ),
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value,
    unmanagedBase := {
      (ThisBuild / baseDirectory).value / "lib"
    }
  )

lazy val cli = project
  .in(file("cli"))
  .enablePlugins(JavaAppPackaging, BuildInfoPlugin)
  .dependsOn(core)
  .settings(
    name := "fit",
    libraryDependencies ++= Seq(
      "com.github.scopt" %% "scopt" % "4.0.0-RC2",
    ),
    Compile / run / fork := true,
    Compile / run / baseDirectory := (ThisBuild / baseDirectory).value,
  )
