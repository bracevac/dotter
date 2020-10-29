name := "normalizer"

version := "0.1"

scalaVersion := "2.13.3"

libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.3.0"
libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.1" % "test"
libraryDependencies += "com.lihaoyi" %% "pprint" % "0.5.9"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.0"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0" % "test"
libraryDependencies += "com.lihaoyi" % "ammonite" % "2.2.0" cross CrossVersion.full

mainClass in (Compile, run) := Some("edot.Repl")

scalacOptions ++= Seq(
  "-Xcheckinit",
  "-deprecation",
  "-language:implicitConversions",
)



