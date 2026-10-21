ThisBuild / scalaVersion := "3.10.0"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Werror")

val munit = "org.scalameta" %% "munit" % "1.1.1"

/** Code that FrFlow lifts must keep method trees (the lifter reads method
  * bodies) and Scaladoc (carried into the generated Lean and the digest).
  */
val modelOptions = Seq("-Yretain-trees", "-Xread-docs")

lazy val root = project
  .in(file("."))
  .aggregate(core, authz)
  .settings(name := "frflow", publish / skip := true)

/** IR, macro lifter, layered DSL, runtime, Lean backend, checker, ledger, reports, CLI. No runtime dependencies. */
lazy val core = project
  .in(file("modules/core"))
  .settings(
    name := "frflow-core",
    libraryDependencies += munit % Test,
    Test / scalacOptions ++= modelOptions
  )

/** Authorization platform: layered model down to an executable implementation.
  * Its integration tests run the full Lean check when `lake` is available.
  */
lazy val authz = project
  .in(file("examples/authz"))
  .dependsOn(core)
  .settings(
    name := "frflow-example-authz",
    publish / skip := true,
    scalacOptions ++= modelOptions,
    libraryDependencies += munit % Test,
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value
  )
