package frflow.project.rocq

import java.nio.file.{Files, Path}

/** The proofs about Ox's scopes and forks (`examples/ox/rocq/Ox`), checked by Rocq: containment of the code read
  * from Ox's TASTy (`Gen.v`) against the JDK's contracts, and the laws of a scope stated from it (`Laws.v`).
  * What `examples/ox/rocq/check.sh` checks.
  */
class OxProofRocqSuite extends munit.FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  private val ox = Path.of("examples/ox/rocq/Ox")
  private val library = List("Threads/Prog", "Threads/Jdk", "Threads/Sem", "Threads/Logic", "Threads/Lang")
  private val proofs = List("Gen", "Ghost", "Facts", "Specs", "Frame", "Updates", "Steps", "Inner", "HerdProofs",
    "ScopeProofs", "Main", "ApiProofs", "Example", "Laws")

  test("Rocq checks containment of Ox's code, and the laws of a scope stated from it".tag(Rocq)) {
    val files = proofs.map(f => s"Ox/$f.v" -> Files.readString(ox.resolve(s"$f.v")))
    assertEquals(ThreadsRocq.failing(files, library), None)
  }
