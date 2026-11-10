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
val catsEffectTestkit = "org.typelevel" %% "cats-effect-testkit" % "3.6.3" % Test
val lawTests = Seq("org.typelevel" %% "cats-kernel-laws" % "2.13.0" % Test,
  "org.typelevel" %% "discipline-munit" % "2.0.0" % Test)

/** The SQLite driver rooms' table is kept in, for the tests that run rooms (eval's and every module's after it). */
val roomsTable = "org.xerial" % "sqlite-jdbc" % "3.46.1.3" % Test

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
// A new project: `sbt "frflowInit toy --as NAME"` (an empty FrModel and its line below; `--as` lists you as the first
// decider); with an AI agent's layer on top, `sbt "frflowInitAgent toy --as NAME"`.
addCommandAlias("frflowInit", "cli/runMain frflow.cli.Init")
addCommandAlias("frflowInitAgent", "agent/runMain frflow.agent.Init")

// The modules (docs/redesign/ARCHITECTURE.md, section 5): each `module(name, libraries*)` under modules/<name>/, sbt
// id `<name>` (but `evaluation`, below), package `frflow.<name>`, its warnings errors. The module graph is written
// here only (section 11).
val strict = Seq("-Wunused:all", "-Wnonunit-statement", "-Wvalue-discard")
def module(name: String, libraries: ModuleID*) = Project(name, file(s"modules/$name"))
  .configs(LeanTest).settings(leanTagged)
  .settings(Keys.name := s"frflow-$name", libraryDependencies ++= munit +: libraries, scalacOptions ++= strict)

lazy val root = project.in(file("."))
  .aggregate(core, dsl, proof, eval, testing, decision, wire, shell, api, cli, web, agent,
    roomsModel, rooms, authModel, auth, keycloakModel, keycloak, crmModel, crm, walletModel, wallet)
  .configs(LeanTest).settings(leanTagged)
  .settings(publish / skip := true)

/** Names, types, the term algebras and core interpreters, the IR, statements, validation, checking, consistency. */
lazy val core = module("core", cats).settings(libraryDependencies ++= lawTests)

/** The DSL a model is written in: terms, nodes, flows, state models, models, macros; its elaboration. */
lazy val dsl = module("dsl", cats).dependsOn(core)
  // Its tests call ordinary methods from lifted code (`lifted.ReadMethods`): the compiler keeps their bodies.
  .settings(Test / scalacOptions += "-Yretain-trees")

/** Obligations, the Lean AST, the one term printer, lowering, layout, reading Lean's output, the judges. */
lazy val proof = module("proof", cats).dependsOn(core % "compile->compile;test->test")

/** The Scala meaning of terms and of plain code: the evaluator, examples, the values a call reads, flows run on
  * models, production's interpreter of flows; the facade `frflow.*` FrFlow's examples are written in. Its tests read
  * core's generated terms and proof's printer (Lean decides each term as the evaluator does). Its sbt id is
  * `evaluation`: `eval` is sbt's own command, so `sbt eval/test` would evaluate `/test` as Scala.
  */
lazy val eval = module("eval", cats, catsEffectKernel, catsEffectStd, catsEffect % Test, roomsTable)
  .withId("evaluation")
  .dependsOn(dsl, proof % "test->test")

/** Generators and what draws them, property tests of plain code against its claims, model tests of implementations,
  * interleavings, the searches for witnesses and refutations, and the examples' runner (an sbt test framework, so
  * `sbt test` runs a project's `FrFlowExamples`). Its tests read FrFlow's examples (examples/<name>).
  */
lazy val testing = module("testing", cats, catsEffect, roomsTable, "org.scala-sbt" % "test-interface" % "1.0",
    munitEffect)
  .settings(libraryDependencies ++= lawTests :+ "org.typelevel" %% "cats-laws" % "2.13.0" % Test,
    testFrameworks += TestFramework("frflow.testing.examples.ExamplesFramework"))
  .dependsOn(eval % "compile->compile;test->test", roomsModel % "test->test", authModel % "test->test",
    keycloakModel % "test->test", crmModel % "test->test", walletModel % "test->test")
  // Its tests hold a model whose service changes a port (`frflow.eval.Desk`), read through its methods' bodies:
  // the compiler keeps them.
  .settings(Test / scalacOptions += "-Yretain-trees")

/** The developer's decisions: content, the ledger, the deciders, review, the rules of each command. */
lazy val decision = module("decision", cats).dependsOn(core)

/** The files FrFlow writes under a project's .frflow/ (the ledger, the deciders' list, checks, tests) and the snapshot
  * the front ends read: rows of its own, and explicit codecs, each file with its version. Only the shell depends on it.
  */
lazy val wire = module("wire", cats, circe, circeParser)
  .settings(libraryDependencies += "org.scalameta" %% "munit-scalacheck" % "1.0.0" % Test)
  .dependsOn(proof, decision, testing)

/** The imperative shell (sbt id `project`, package `frflow.project`; `project` itself names sbt's own method here): the
  * algebras of the project's files, Lean, git, the keys and the ledger's store, each with its live and in-memory
  * interpreters; the analysis of a project (contents, fingerprints, standings), and the programs (check, status,
  * decide, export) over them. Its tests read FrFlow's examples (examples/<name>).
  */
lazy val shell = module("project", (Seq(cats, catsEffect, munitEffect, catsEffectTestkit, roomsTable) ++ fs2)*)
  .dependsOn(proof, testing % "compile->compile;test->test", decision, wire)

/** The API front ends call: three algebras (`Reading`, `Deciding`, `Proving`) over a project, the views they return
  * (`api.view`, `api.node`: front ends see nothing else), and the live and in-memory interpreters. Its tests read the
  * shell's projects in memory.
  */
lazy val api = module("api", (Seq(cats, catsEffect, munitEffect, roomsTable) ++ fs2)*)
  .settings(libraryDependencies ++= lawTests)
  .dependsOn(shell % "compile->compile;test->test")

/** The command line a project's main object extends (`FrFlowApp`, the composition root): its commands, colors, the
  * interactive review, and `init`; layers on top add their commands (`CliExtension`). Its tests read the API's.
  */
lazy val cli = module("cli", cats, catsEffect, roomsTable, decline, munitEffect)
  .settings(forkedAtRoot)
  .dependsOn(api % "compile->compile;test->test")

/** `init` runs forked from the build's directory (`frflowInit`), so it exits with its own code. */
def forkedAtRoot: Seq[Setting[?]] = Seq(run / fork := true, run / baseDirectory := (ThisBuild / baseDirectory).value)

/** The web view (`serve`): the page, and routes onto the API, over http4s on localhost; layers on top add routes and
  * a script (`WebExtension`). The CLI does not depend on it.
  */
lazy val web = module("web", (Seq(catsEffect, circe, munitEffect, roomsTable) ++ http4s)*)
  .dependsOn(api % "compile->compile;test->test")

/** A layer on top for an AI agent building the system: the conversation a project starts from, the developer's
  * requests and the agent's answers, its queue, `context`, their commands and web panels. It proposes and asks;
  * deciding stays the developer's.
  */
lazy val agent = module("agent",
    (Seq(cats, catsEffect, circe, circeParser, decline, munitEffect, roomsTable) ++ http4s)*)
  .settings(forkedAtRoot)
  .dependsOn(cli % "compile->compile;test->test", web % "compile->compile;test->test")

/** The java command that runs a project's CLI on a terminal (colors, the interactive review): what `bin/frflow` runs. */
val cliLauncher = taskKey[File]("Writes the java command running this project's CLI, for bin/frflow")
val serve = inputKey[Unit]("The project's web view on localhost, until stopped: serve [--port N] [--as NAME]")

/** A project, as `init` writes its line (`frflow.cli.Init`), under examples/<name>/: its main object runs the CLI with
  * its examples' classes on the classpath (`frflow.tests` names where they are), `cliLauncher` writes that java command
  * for `bin/frflow`, and `serve` runs its web view; `layers`, the layers on top it uses (the AI agent's by default).
  */
def example(name: String, layers: Seq[ClasspathDep[ProjectReference]] = Seq(agent)) =
  commandLine(Project(name, file(s"examples/$name")), layers, Def.setting((Test / classDirectory).value))

/** One of FrFlow's own examples, in two projects, so that FrFlow's suites can test it with no cycle in the build: its
  * model (sbt id `<name>Model`, under examples/<name>: its statements and code in src/main, its examples in src/test,
  * its proofs in lean/Proofs), which testing's tests depend on; and its command line (`<name>`, under
  * examples/<name>/app: its main object alone), made as `example` makes one, over the model.
  */
def exampleModel(name: String) = Project(s"${name}Model", file(s"examples/$name"))
  .configs(LeanTest).settings(leanTagged)
  .settings(Keys.name := s"frflow-example-$name", scalacOptions ++= strict, publish / skip := true,
    libraryDependencies ++= Seq(munit, catsEffect, "org.xerial" % "sqlite-jdbc" % "3.46.1.3"))
  .dependsOn(eval)

def exampleApp(name: String, model: Project, layers: Seq[ClasspathDep[ProjectReference]] = Seq(agent)) =
  commandLine(Project(name, file(s"examples/$name/app")), layers, Def.setting((model / Test / classDirectory).value))
    .dependsOn(model % "compile->compile;test->test")
    .settings(Compile / run / mainClass := Some(s"$name.${name}Cli"))

def commandLine(p: Project, layers: Seq[ClasspathDep[ProjectReference]], tests: Def.Initialize[File]) = p
  .dependsOn((Seq[ClasspathDep[ProjectReference]](cli, web) ++ layers)*)
  .configs(LeanTest).settings(leanTagged)
  .settings(
    libraryDependencies += munit, publish / skip := true, run / fork := true, Test / fork := true,
    run / javaOptions ++= Seq("-Dstdout.encoding=UTF-8", "-Dstderr.encoding=UTF-8", "-Dfile.encoding=UTF-8"),
    run / javaOptions += "-Dfrflow.tests=" + tests.value.getAbsolutePath,
    Compile / run := Defaults.runTask(Test / fullClasspath, Compile / run / mainClass, Compile / run / runner)
      .evaluated,
    Compile / runMain := Defaults.runMainTask(Test / fullClasspath, Compile / run / runner).evaluated,
    run / baseDirectory := (ThisBuild / baseDirectory).value,
    Test / baseDirectory := (ThisBuild / baseDirectory).value,
    cliLauncher := {
      val launch = target.value / "frflow.launch"
      val main = (Compile / run / mainClass).value.getOrElse(sys.error(s"${Keys.name.value} has no main class"))
      val classpath = (Test / fullClasspath).value.files.mkString(java.io.File.pathSeparator)
      IO.writeLines(launch, (run / javaOptions).value ++ Seq("-cp", classpath, main))
      launch
    },
    serve := Def.inputTaskDyn {
      val args = complete.DefaultParsers.spaceDelimited("[--port N] [--as NAME]").parsed
      val main = (Compile / run / mainClass).value.getOrElse(sys.error(s"${Keys.name.value} has no main class"))
      (Compile / runMain).toTask((Seq("frflow.web.Serve", main) ++ args).mkString(" ", " ", ""))
    }.evaluated)

/** Booking meeting rooms: a request is granted exactly when its room is free; the README's example. */
lazy val roomsModel = exampleModel("rooms")
lazy val rooms = exampleApp("rooms", roomsModel, layers = Nil)

/** Access control: who can access what, refined through grants, sessions and requests to proven code. */
lazy val authModel = exampleModel("auth")
lazy val auth = exampleApp("auth", authModel)

/** A Keycloak-like authentication server: realms, sign-in, token introspection, sign-out. */
lazy val keycloakModel = exampleModel("keycloak")
lazy val keycloak = exampleApp("keycloak", keycloakModel)

/** A multi-tenant CRM: users find exactly their company's and shared records, write only their company's. */
lazy val crmModel = exampleModel("crm")
lazy val crm = exampleApp("crm", crmModel)

/** People, teams, documents and folders: who can view and edit what, and who may change it. */

/** A wallet: transfers between accounts, never overdrawn, carried out once, whatever calls run at once. Its services
  * are plain Scala over a store, read by FrFlow (`updating`, `interleaving`): the compiler keeps method bodies, and
  * checks each store is its service's alone (Scala's capture and separation checking, experimental).
  */
val readServices = Seq(scalacOptions ++= Seq("-Yretain-trees", "-experimental"))
lazy val walletModel = exampleModel("wallet").settings(readServices)
lazy val wallet = exampleApp("wallet", walletModel, layers = Nil).settings(readServices)
