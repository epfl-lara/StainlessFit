
enablePlugins(GitVersioning)
git.useGitDescribe := true

ThisBuild / organization := "ch.epfl.lara"
ThisBuild / scalaVersion := "2.12.9"

ThisBuild / resolvers ++= Seq(
  Resolver.bintrayRepo("epfl-lara", "maven")
)

ThisBuild / scalacOptions ++= Seq(
  "-encoding", "UTF-8",
  "-deprecation",
  "-unchecked",
  "-feature"
)

lazy val cli = project
  .in(file("cli"))
  .enablePlugins(JavaAppPackaging, BuildInfoPlugin)
  .settings(
    name := "stainlesscore-cli",
    libraryDependencies ++= Seq(
      "com.github.scopt" %% "scopt" % "4.0.0-RC2",
    ),
    Compile / run / fork := true,
    Compile / run / baseDirectory := (ThisBuild / baseDirectory).value
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
    Test / baseDirectory := (ThisBuild / baseDirectory).value
  )
  .dependsOn(verified)

lazy val verified = project
  .in(file("verified"))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "stainlesscore-verified",
    stainlessEnabled := false,
    Compile / unmanagedBase := (ThisBuild / baseDirectory).value / "unmanaged",
    Compile / unmanagedSourceDirectories += {
      (ThisBuild / baseDirectory).value / "unmanaged"
    }
  )
