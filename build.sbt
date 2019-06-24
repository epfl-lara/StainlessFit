scalaVersion := "2.12.7"

resolvers ++= Seq(
    Resolver.bintrayRepo("epfl-lara", "maven")
)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "3.0.8" % "test",
  "ch.epfl.lara" % "scallion_2.12" % "0.1"
)

