// A build of its own, outside FrFlow's: it runs Ox 1.1.0 to see two behaviours the proof predicts.
//   cd examples/ox/probe && sbt "run 200000"
ThisBuild / scalaVersion := "3.10.0"
libraryDependencies += "com.softwaremill.ox" %% "core" % "1.1.0"
fork := true
