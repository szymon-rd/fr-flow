package frflow.project

/** A test of a live interpreter (the disk, git, Lean's `lake`) or of a project end to end: run by `sbt Lean/test`, left
  * out of `sbt test`, whose suites run on the in-memory interpreters only.
  */
val Live: munit.Tag = munit.Tag("Lean")
