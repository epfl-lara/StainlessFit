ThisBuild / scalaVersion := "2.12.8"

ThisBuild / resolvers ++= Seq(
    Resolver.bintrayRepo("epfl-lara", "maven")
)

ThisBuild / libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.0.8" % "test",
  "ch.epfl.lara" %% "scallion" % "0.1"
)

lazy val core = project
  .in(file("core"))
  .settings(
    name := "stainlesscore",
  )
  .dependsOn(verified)

lazy val verified = project
  .in(file("verified"))
  .settings(
    name := "stainlesscore-verified"
  )
