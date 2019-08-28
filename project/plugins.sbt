resolvers ++= Seq(
  Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
  Resolver.bintrayRepo("epfl-lara", "princess"),
  "uuverifiers" at "http://logicrunch.research.it.uu.se/maven",
)

val StainlessVersion = "0.4.0"

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % StainlessVersion)

addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.9.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.4.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

// avoids warning from sbt-git, see https://github.com/sbt/sbt-git#known-issues
