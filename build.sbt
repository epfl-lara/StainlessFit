
enablePlugins(GitVersioning)
git.useGitDescribe := true

ThisBuild / organization := "ch.epfl.lara"
ThisBuild / scalaVersion := "2.12.8"

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
  )
  .dependsOn(core)

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainlesscore",
    libraryDependencies ++= Seq(
      "ch.epfl.lara"  %% "scallion"  % "0.1",
      "org.scalatest" %% "scalatest" % "3.0.8" % "test",
    ),
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
