
enablePlugins(GitVersioning)
git.useGitDescribe := true

ThisBuild / organization := "ch.epfl.lara"
ThisBuild / scalaVersion := "2.13.1"

ThisBuild / resolvers ++= Seq(
  Resolver.bintrayRepo("epfl-lara", "maven")
)

ThisBuild / scalacOptions ++= Seq(
  "-encoding", "UTF-8",
  "-deprecation",
  "-unchecked",
  "-feature"
)

ThisBuild / maxErrors := 3

lazy val cli = project
  .in(file("cli"))
  .enablePlugins(JavaAppPackaging, BuildInfoPlugin)
  .settings(
    name := "stainlesscore-cli",
    assemblyJarName in assembly := "stainlesscore-cli.jar",
    test in assembly := {},
    libraryDependencies ++= Seq(
      "com.github.scopt" %% "scopt" % "4.0.0-RC2",
    ),
    Compile / run / fork := true,
    Compile / run / baseDirectory := (ThisBuild / baseDirectory).value,
    unmanagedBase := {
      (ThisBuild / baseDirectory).value / "lib"
    }
  )
  .dependsOn(core)

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainlesscore",
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.0.8" % "test",
    ),
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value,
    unmanagedBase := {
      (ThisBuild / baseDirectory).value / "lib"
    }
  )
