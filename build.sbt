
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

ThisBuild / maxErrors := 5

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainless-fit",
    assemblyJarName in assembly := "fit.jar",
    test in assembly := {},
    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.0.8" % "test",
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
