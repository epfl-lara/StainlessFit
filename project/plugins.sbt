resolvers ++= Seq(
  Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
  Resolver.bintrayRepo("epfl-lara", "princess"),
  "uuverifiers" at "http://logicrunch.research.it.uu.se/maven",
)

val StainlessVersion = "0.3.1"

addSbtPlugin("ch.epfl.lara" % "sbt-stainless" % StainlessVersion)

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.10")
