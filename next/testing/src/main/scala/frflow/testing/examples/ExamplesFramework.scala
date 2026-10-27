package frflow.testing.examples

import sbt.testing.{Fingerprint, Framework, Runner, SubclassFingerprint}

/** The examples' runner: an sbt test framework, so `sbt test` runs every class extending `FrFlowExamples` in a
  * project's tests, each example a test checked against the code (`Verdicts`). A project's build names it beside
  * munit: `testFrameworks += TestFramework("frflow.testing.examples.ExamplesFramework")`.
  */
final class ExamplesFramework extends Framework:
  def name(): String = "FrFlow examples"
  def fingerprints(): Array[Fingerprint] = Array(ExamplesFramework.Written)
  def runner(args: Array[String], remoteArgs: Array[String], loader: ClassLoader): Runner =
    ExamplesRunner(args, remoteArgs, loader)

object ExamplesFramework:
  /** A class of examples: one extending `FrFlowExamples`, made with no arguments. */
  object Written extends SubclassFingerprint:
    def isModule(): Boolean = false
    def superclassName(): String = "frflow.dsl.example.FrFlowExamples"
    def requireNoArgConstructor(): Boolean = true
