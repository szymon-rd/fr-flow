package frflow
package lean

import frflow.fixtures.*
import frflow.protocol.{ObligationName, Sha}

/** The generated Lean, byte for byte, on fixtures: a change to it moves every cached proof and decision. The
  * whole of it is pinned by a hash; one file of each kind is recorded, to read and to diff.
  */
class GoldenSuite extends munit.FunSuite:

  /** Every file of a FrModel's Lean, the proof file stubs of its nodes and what check hashes are made of. */
  private def sections(kb: FrModel): List[(String, String)] =
    val g = Generate(kb)
    val perNode = kb.nodes.filter(g.formal).flatMap(n => List(
      s"proof file of ${n.id}" -> g.proofFile(n, List(ObligationName.Complete, ObligationName.Impl)),
      s"used by ${n.id}" -> (g.declarationsUsedBy(n) ++ g.sourcesUsedBy(n)).mkString("\n"),
      s"not evaluated of ${n.id}" -> g.evals(n)._2.mkString("\n")))
    g.files.toList.sortBy(_._1) ++ perNode :+ ("lakefile" -> g.lakefile("../../lean"))

  private def text(ss: List[(String, String)]): String = ss.map((p, s) => s"=== $p ===\n$s").mkString("\n")

  private val hashes = List(shelfKb -> "eddf3bcfce03b7482e9c30c7c11b9559dd629811879e2ccf0bc959eb4b83e5c2",
    callsKb -> "fa75699897724c96d8846ef8c9ef0b1a9283c9cd65650ab925c4aee78ea5cbae")

  test("the whole Lean of each fixture is as recorded, byte for byte") {
    hashes.foreach { (kb, hash) =>
      val got = text(sections(kb))
      val file = java.nio.file.Paths.get(s"target/golden-${kb.name}.lean.txt").toAbsolutePath
      if Sha(got) != hash then java.nio.file.Files.writeString(file, got)
      assertEquals(Sha(got), hash, s"the Lean of ${kb.name} changed: it is in $file. If the change is meant, check the " +
        "recorded files below still read right, regenerate golden/calls.lean.txt from it, and record the new hash here")
    }
  }

  /** One file of each kind: a node with parts, proven code, the root of the code, the vocabulary, a proof
    * file, what a decision is bound to, and the examples evaluated (not the probes).
    */
  private val recorded = List("PickedAgain/Spec", "PickedAgain/Auto", "PickedAgain/Theorems", "PickedAgain/Checks",
    "PickPromise/Impl", "PickedAgain/RootImpl", "Types", "Domain", "Domain/Def_viaPick", "Again/Eval")
    .map(m => s"FrFlowGen/Calls/$m.lean") ++
    List("proof file of PickedAgain", "used by Again")

  test("one file of each kind reads as recorded") {
    val got = sections(callsKb).filter((p, _) => recorded.contains(p)).map { (p, s) =>
      p -> (if p.endsWith("Eval.lean") then s.take(s.indexOf("/-- probe 1 -/")) else s)
    }
    assertEquals(got.map(_._1).sorted, recorded.sorted)
    val expected = scala.io.Source.fromResource("golden/calls.lean.txt")(using scala.io.Codec.UTF8).mkString
    assertNoDiff(text(got), expected)
    assert(text(got) == expected, "the same lines, but not the same bytes (whitespace at the ends of lines?)")
  }
