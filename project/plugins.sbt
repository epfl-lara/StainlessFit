resolvers ++= Seq(
  Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
  Resolver.bintrayRepo("epfl-lara", "princess"),
  "uuverifiers" at "http://logicrunch.research.it.uu.se/maven",
)

val StainlessVersion = "0.3.1"

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % StainlessVersion)

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.3.25")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
