// The planned core of FrFlow's redesign (r43): one sbt project per target module, sources under src/<module>/.
// It compiles to show the types hold together; bodies that do not carry the design are `???`.
ThisBuild / scalaVersion := "3.10.0"
ThisBuild / scalacOptions ++= Seq("-deprecation", "-feature", "-Werror", "-Wunused:all", "-Wnonunit-statement", "-Wvalue-discard")

val cats = "org.typelevel" %% "cats-core" % "2.13.0"
val catsEffect = "org.typelevel" %% "cats-effect" % "3.6.3"
val catsEffectKernel = "org.typelevel" %% "cats-effect-kernel" % "3.6.3"
val catsEffectStd = "org.typelevel" %% "cats-effect-std" % "3.6.3"
val fs2 = "co.fs2" %% "fs2-core" % "3.12.2"

def module(name: String, libs: ModuleID*) = Project(name, file(s"src/$name"))
  .settings(Keys.name := s"frflow-$name")
  .settings(Compile / scalaSource := baseDirectory.value, libraryDependencies ++= libs)
  .settings(target := (ThisBuild / baseDirectory).value / "target" / name)

/** A module's munit suites, under test/<dir>/. */
def suites(dir: String) = Seq(
  libraryDependencies += "org.scalameta" %% "munit" % "1.1.1" % Test,
  Test / scalaSource := (ThisBuild / baseDirectory).value / "test" / dir)

/** The IR: vocabulary, expressions, programs, statements, the refinement graph, code attachments; and the analyses. */
lazy val core = module("core", cats)
/** The DSL a model is written in, and its elaboration into the IR. */
lazy val dsl = module("dsl", cats).dependsOn(core).settings(suites("dsl"))
/** Obligations (what Lean is asked), the Lean AST, its printing, reading Lean's output, and the judges. */
lazy val proof = module("proof", cats).dependsOn(core).settings(suites("proof")).settings(
  Test / resourceDirectory := (ThisBuild / baseDirectory).value / "test" / "proof" / "resources")
/** The Scala meaning of the IR and of the plain-code path: terms as functions, flows run (on the models, in a `Sync`
  * against bound implementations), examples. */
lazy val evaluation = module("eval", cats, catsEffectKernel, catsEffectStd).withId("evaluation").dependsOn(dsl)
  .settings(suites("eval"))
/** The running system: services checked against their contracts, flows run concurrently, the facade. */
lazy val runtime = module("runtime", cats, catsEffect).dependsOn(evaluation % "compile->compile;test->test")
  .settings(suites("runtime"))
/** Property tests of code against contracts and models. */
lazy val testing = module("testing", cats, catsEffect).dependsOn(evaluation)
/** Decisions: contents, the ledger, review states, the decision rules. Of `core`, only names and `graph.Walk`. */
lazy val decision = module("decision", cats).dependsOn(core).settings(suites("decision"))
/** The wire formats: the snapshot by kind, and (not planned here) the codecs of the ledger, checks and tests. */
lazy val wire = module("wire", cats).dependsOn(proof, decision, testing)
/** The imperative shell: workspace, Lean, git, keys, the pipeline of phases, code fingerprints. */
lazy val project = module("project", cats, catsEffect, fs2).dependsOn(proof, testing, decision, wire)
  .settings(suites("project"))
/** The API front ends call. */
lazy val api = module("api", cats, catsEffect, fs2).dependsOn(project)

lazy val root = Project("root", file(".")).aggregate(core, dsl, proof, evaluation, runtime, testing, decision, wire, project, api)
