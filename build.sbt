ThisBuild / scalaVersion := "3.10.0"
ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Werror", "-language:implicitConversions")

// Library versions, shared by every module.
val circe = "io.circe" %% "circe-core" % "0.14.17"
val circeParser = "io.circe" %% "circe-parser" % "0.14.17"
val cats = "org.typelevel" %% "cats-core" % "2.13.0"
val catsEffect = "org.typelevel" %% "cats-effect" % "3.6.3"
val catsEffectKernel = "org.typelevel" %% "cats-effect-kernel" % "3.6.3"
val catsEffectStd = "org.typelevel" %% "cats-effect-std" % "3.6.3"
val fs2 = Seq("co.fs2" %% "fs2-core" % "3.12.2", "co.fs2" %% "fs2-io" % "3.12.2")
val decline = "com.monovore" %% "decline" % "2.5.0"
val http4s = Seq("http4s-ember-server", "http4s-dsl", "http4s-circe").map("org.http4s" %% _ % "0.23.33") :+
  // Ember logs through SLF4J and warns on start without a binding. The routes handle their own failures, so its log is discarded.
  "org.slf4j" % "slf4j-nop" % "1.7.36"
val munit = "org.scalameta" %% "munit" % "1.1.1" % Test
val munitEffect = "org.typelevel" %% "munit-cats-effect" % "2.1.0" % Test

// Tests tagged `Lean` run Lean end to end (minutes): plain `sbt test` leaves them out, `sbt leanTest` runs them,
// `sbt testAll` runs both.
lazy val LeanTest = config("lean").extend(Test)
val withoutLean = Tests.Argument(TestFrameworks.MUnit, "--exclude-tags=Lean")
def leanTagged: Seq[Setting[?]] = inConfig(LeanTest)(Defaults.testTasks) ++ Seq(
  Test / testOptions += withoutLean,
  LeanTest / testOptions := (LeanTest / testOptions).value.filterNot(_ == withoutLean) :+
    Tests.Argument(TestFrameworks.MUnit, "--include-tags=Lean"))
addCommandAlias("leanTest", "Lean/test")
addCommandAlias("testAll", "; test; Lean/test")
// A new project: `sbt "frflowInit toy"` (an empty knowledge base and its line below); with an AI agent's layer on top,
// `sbt "frflowInitAgent toy"` (the same, its main object passing the layer; the idea is then told in chat).
addCommandAlias("frflowInit", "cli/runMain frflow.cli.Init")
addCommandAlias("frflowInitAgent", "agent/runMain frflow.agent.Init")

lazy val root = project.in(file("."))
  .aggregate((Seq[ProjectReference](model, protocol, lean, ledger, check, api, cli, web, testkit, agent, auth, crm,
    keycloak, sharing, rooms, referenceCapture) ++ nextModules)*)
  .configs(LeanTest).settings(leanTagged)
  .settings(publish / skip := true)

def module(name: String, libraries: ModuleID*) = Project(name, file(s"modules/$name"))
  .configs(LeanTest).settings(leanTagged)
  .settings(Keys.name := s"frflow-$name", libraryDependencies ++= munit +: libraries)

// The rebuild (docs/redesign/ARCHITECTURE.md, section 9): each new module is `nextModule(name, libraries*)` under
// next/<name>/, sbt id `next-<name>`, package `frflow.<name>`, with the planned build's warnings as errors. A step
// adds its `lazy val` in its slot below and its name in its slot of `nextModules`, which the root aggregates.
val nextFlags = Seq("-Wunused:all", "-Wnonunit-statement", "-Wvalue-discard")
val lawTests = Seq("org.typelevel" %% "cats-kernel-laws" % "2.13.0" % Test,
  "org.typelevel" %% "discipline-munit" % "2.0.0" % Test)
def nextModules: Seq[ProjectReference] = Seq(
  nextCore,

  nextDsl, // step 2

  // step 3: nextProof
  nextProof,

  // step 4: nextEval
  nextEval,

  // step 5: nextTesting
  nextTesting,

  nextDecision,

  // step 7: nextWire
  nextWire,

  // step 8: nextProject

  // step 9: nextApi

  // step 10: nextCli, nextWeb, nextAgent
)
def nextModule(name: String, libraries: ModuleID*) = Project(s"next-$name", file(s"next/$name"))
  .configs(LeanTest).settings(leanTagged)
  .settings(Keys.name := s"frflow-next-$name", libraryDependencies ++= munit +: libraries,
    scalacOptions ++= nextFlags, publish / skip := true)

/** Names, types, the term algebras and core interpreters, the IR, statements, validation, checking, consistency. */
lazy val nextCore = nextModule("core", cats).settings(libraryDependencies ++= lawTests)

/** The DSL a model is written in: terms, nodes, programs over boundaries, models, macros; its elaboration. */
lazy val nextDsl = nextModule("dsl", cats).dependsOn(nextCore)

// next-proof (step 3)
/** Obligations, the Lean AST, the one term printer, lowering, layout, reading Lean's output, the judges. */
lazy val nextProof = nextModule("proof", cats).dependsOn(nextCore % "compile->compile;test->test")

// next-eval (step 4)
/** The Scala meaning of terms and of plain code: the evaluator, examples, the values a call reads, recorded programs
  * run on models, production's interpreter of programs; the facade `frflow.*`, and the examples written in it. Its
  * tests read core's generated terms and proof's printer (Lean decides each term as the evaluator does). */
lazy val nextEval = nextModule("eval", cats, catsEffectKernel, catsEffectStd, catsEffect % Test)
  .dependsOn(nextDsl, nextProof % "test->test")

// next-testing (step 5)
/** Generators and what draws them, property tests of plain code against its claims, model tests of implementations,
  * interleavings, the searches for witnesses and refutations, and the examples' runner (an sbt test framework, so
  * `sbt test` runs a project's `FrFlowExamples`). Its tests read the examples written in eval's tests. */
lazy val nextTesting = nextModule("testing", cats, catsEffect, "org.scala-sbt" % "test-interface" % "1.0", munitEffect)
  .settings(libraryDependencies ++= lawTests :+ "org.typelevel" %% "cats-laws" % "2.13.0" % Test,
    testFrameworks += TestFramework("frflow.testing.examples.ExamplesFramework"))
  .dependsOn(nextEval % "compile->compile;test->test")

lazy val nextDecision = nextModule("decision", cats).dependsOn(nextCore)

// next-wire (step 7)
/** The files FrFlow writes under a project's .frflow/ (the ledger, the deciders' list, checks, tests) and the snapshot
  * the front ends read: rows of its own, and explicit codecs, each file with its version. Only the shell depends on it. */
lazy val nextWire = nextModule("wire", cats, circe, circeParser)
  .settings(libraryDependencies += "org.scalameta" %% "munit-scalacheck" % "1.0.0" % Test)
  .dependsOn(nextProof, nextDecision, nextTesting)

// next-project (step 8)

// next-api (step 9)

// next-cli, next-web, next-agent (step 10)

// FrFlow's core: the modules below up to `web`, usable on their own. `agent` is a layer on top; no core module depends on it.

/** The DSL: terms, flows, nodes, the knowledge base, the runtime checks (package `frflow`). */
lazy val model = module("model", cats, catsEffectKernel, catsEffect).dependsOn(protocol)

/** The data crossing modules and files: the snapshot, the review, the ledger and checks, with their JSON codecs; ids and
  * statuses (package `frflow.protocol`).
  */
lazy val protocol = module("protocol", circe, circeParser % Test)

/** The Lean of a knowledge base, and reading Lean's output. */
lazy val lean = module("lean", cats).dependsOn(model % "compile->compile;test->test", protocol)

/** The developer's decisions: review states, decide, signatures, reports; the ledger's and keys' files. */
lazy val ledger = module("ledger", cats, catsEffect, circe, circeParser, munitEffect).dependsOn(protocol)

/** Rendering and checking a knowledge base against Lean; the snapshot; git. */
lazy val check = module("check", (Seq(cats, catsEffect, circe, circeParser, munitEffect) ++ fs2)*)
  .dependsOn(lean % "compile->compile;test->test", ledger)

/** The API the front ends (the CLI, the web view) call, over `IO`. */
lazy val api = module("api", cats, catsEffect, circe, munitEffect).dependsOn(check % "compile->compile;test->test")

/** The command line a project's main object extends (`FrFlowApp`): commands, colors, interactive review; layers on top add
  * their commands (`CliExtension`).
  */
lazy val cli = module("cli", cats, catsEffect, circe, decline, munitEffect).dependsOn(api % "compile->compile;test->test")

/** The web view (`serve`): the page, and routes onto the API, over http4s on localhost; layers on top add routes and a
  * script (`WebExtension`). The CLI does not depend on it.
  */
lazy val web = module("web", (Seq(catsEffect, circe, munitEffect) ++ http4s)*).dependsOn(api % "compile->compile;test->test")

/** Examples written as tests (`FrFlowExamples`): run by munit, and read by `check` from a project's test classes. */
lazy val testkit = module("testkit", "org.scalameta" %% "munit" % "1.1.1").dependsOn(model)

/** A layer on top of the core for an AI agent building the system: the conversation a project starts from, the developer's
  * requests and the agent's answers, the agent's queue, `context`, their commands and web panels (package `frflow.agent`).
  */
lazy val agent = module("agent", (Seq(cats, catsEffect, circe, circeParser, decline, munitEffect) ++ http4s)*)
  .dependsOn(cli % "compile->compile;test->test", web % "compile->compile;test->test", ledger % "test->test")

/** The java command that runs a project's CLI on a terminal (colors, the interactive review): what `bin/frflow` runs. */
val cliLauncher = taskKey[File]("Writes the java command running this project's CLI, for bin/frflow")
val serve = inputKey[Unit]("The project's web view on localhost, until stopped: serve [--port N] [--as NAME]")

/** A project; `layers`, the layers on top on its classpath (the AI agent's by default; none for a core-only project). */
def example(name: String, layers: Seq[ClasspathDep[ProjectReference]] = Seq(agent)) = Project(name, file(s"examples/$name"))
  .dependsOn((Seq[ClasspathDep[ProjectReference]](cli, web, testkit % Test) ++ layers)*)
  .configs(LeanTest).settings(leanTagged)
  .settings(
    libraryDependencies ++= Seq(munit, munitEffect),
    publish / skip := true,
    run / fork := true,
    // The CLI's output (read by agents) is UTF-8 whatever the locale.
    run / javaOptions ++= Seq("-Dstdout.encoding=UTF-8", "-Dstderr.encoding=UTF-8", "-Dfile.encoding=UTF-8"),
    // Every source the build compiles, so code in a source directory added here is governed too.
    run / javaOptions += "-Dfrflow.sources=" + (Compile / sources).value.map(_.getAbsolutePath).mkString(java.io.File.pathSeparator),
    // The examples written as tests (`FrFlowExamples`), which `check` reads: the test classes are on the CLI's
    // classpath.
    run / javaOptions += "-Dfrflow.tests=" + (Test / classDirectory).value.getAbsolutePath,
    Compile / run :=
      Defaults.runTask(Test / fullClasspath, Compile / run / mainClass, Compile / run / runner).evaluated,
    Compile / runMain := Defaults.runMainTask(Test / fullClasspath, Compile / run / runner).evaluated,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    cliLauncher := {
      val launch = target.value / "frflow.launch"
      val main = (Compile / run / mainClass).value.getOrElse(sys.error(s"${Keys.name.value} has no main class"))
      val classpath = (Test / fullClasspath).value.files.mkString(java.io.File.pathSeparator)
      IO.writeLines(launch, (run / javaOptions).value ++ Seq("-cp", classpath, main))
      launch
    },
    // The web view runs the project's main object (its knowledge base) in a forked JVM, over the API the CLI uses.
    serve := Def.inputTaskDyn {
      val args = complete.DefaultParsers.spaceDelimited("[--port N] [--as NAME]").parsed
      val main = (Compile / run / mainClass).value.getOrElse(sys.error(s"${Keys.name.value} has no main class"))
      (Compile / runMain).toTask((Seq("frflow.web.Serve", main) ++ args).mkString(" ", " ", ""))
    }.evaluated,
    Test / fork := true,
    Test / baseDirectory := (ThisBuild / baseDirectory).value
  )

/** Access control: who can access what, refined through grants, sessions and requests to proven code. */
lazy val auth = example("auth")

/** A multi-tenant CRM: one purpose (users find exactly their company's and shared records, write only
  * their company's), refined through the domain to proven code, served over HTTP from SQLite.
  */
lazy val crm = example("crm").settings(libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.46.1.3",
  Compile / run / mainClass := Some("crm.crmCli"))

/** A synthetic project, generated by `bench/generate.py N`, to measure FrFlow as it grows (not built by default). */
lazy val scale = example("scale")

/** A Keycloak-like authentication server: realms, sign-in, token introspection, sign-out. */
lazy val keycloak = example("keycloak").settings(Compile / run / mainClass := Some("keycloak.keycloakCli"))


/** People, teams, documents and folders: who can view and edit what, and who may change it. */
lazy val sharing = example("sharing").settings(libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.46.1.3",
  Compile / run / mainClass := Some("sharing.sharingCli"))

/** Booking meeting rooms: a request is granted exactly when its room is free; the README's example. */
lazy val rooms = example("rooms", layers = Nil).settings(libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.46.1.3")

/** Today's outputs recorded under `reference/` for the rebuild (step 0): `python3 reference/capture.py EXAMPLE` runs
  * it; this project holds the examples' seeded bugs, run as their suites seed them.
  */
lazy val referenceCapture = Project("referenceCapture", file("reference/capture"))
  .dependsOn(auth, crm, keycloak, sharing)
  .configs(LeanTest).settings(leanTagged)
  .settings(publish / skip := true, run / fork := true, run / baseDirectory := (ThisBuild / baseDirectory).value,
    run / javaOptions ++= Seq("-Dstdout.encoding=UTF-8", "-Dfile.encoding=UTF-8", "-Duser.timezone=UTC"))
