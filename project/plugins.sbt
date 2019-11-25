resolvers ++= Seq(
  Resolver.bintrayRepo("epfl-lara", "princess"),
  Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
  ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven").withAllowInsecureProtocol(true),
)

val StainlessVersion = "0.6.1"

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % StainlessVersion)

addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.9.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.4.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.10")
