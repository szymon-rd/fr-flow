package frflow.project

/** A test of a live interpreter (the disk, git, Rocq) or of a project end to end: run by `sbt rocqTest`, left out of
  * `sbt test`, whose suites run on the in-memory interpreters only.
  */
val Live: munit.Tag = munit.Tag("Rocq")
