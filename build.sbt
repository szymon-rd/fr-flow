ThisBuild / scalaVersion := "3.10.0"
ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Werror")

val munit = "org.scalameta" %% "munit" % "1.1.1" % Test

lazy val root = project.in(file(".")).aggregate(core, wallet).settings(publish / skip := true)

/** The FrFlow library: nodes, the Scala-to-Lean translation, the checker, the CLI. */
lazy val core = project.in(file("core")).settings(name := "frflow", libraryDependencies += munit)

/** Example: a wallet, from the developer's idea to a proven chain of nodes. */
lazy val wallet = project
  .in(file("examples/wallet"))
  .dependsOn(core)
  .settings(
    libraryDependencies += munit,
    publish / skip := true,
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value
  )
