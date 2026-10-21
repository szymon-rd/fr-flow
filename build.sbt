ThisBuild / scalaVersion := "3.10.0"
ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Werror")

val munit = "org.scalameta" %% "munit" % "1.1.1" % Test

lazy val root = project.in(file(".")).aggregate(core, tools, auth, crm).settings(publish / skip := true)

/** The FrFlow library: nodes, the Scala-to-Lean translation, the checker, the CLI. */
lazy val core = project.in(file("core")).settings(name := "frflow", libraryDependencies += munit)

/** The browser (where the developer decides) and the MCP server (how agents work). Run with `bin/frflow`. */
lazy val tools = project.in(file("tools"))
  .dependsOn(core)
  .settings(name := "frflow-tools", libraryDependencies += munit, publish / skip := true, Test / fork := true)

def example(name: String) = Project(name, file(s"examples/$name"))
  .dependsOn(core)
  .settings(
    libraryDependencies += munit,
    publish / skip := true,
    run / fork := true,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value
  )

/** Access control: no unauthorized access, from the generic idea to an enforced implementation. */
lazy val auth = example("auth")

/** A multi-tenant CRM: tenant isolation, from the generic idea to an enforced implementation. */
lazy val crm = example("crm")
