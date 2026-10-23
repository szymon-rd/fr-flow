package frflow
package lean

import frflow.fixtures.*

/** The generated Lean, byte for byte, on fixtures: a change to it moves every cached proof and decision. */
class GoldenSuite extends munit.FunSuite:

  /** Every file of a knowledge base's Lean, with the proof file stubs of its nodes and what check
    * hashes are made of, as one text.
    */
  private def rendered(g: Generate, kb: KnowledgeBase): String =
    val files = g.files.toList.sortBy(_._1).map((p, s) => s"=== $p ===\n$s")
    val perNode = kb.nodes.filter(g.formal).flatMap(n => List(
      s"=== proof file of ${n.id} ===\n${g.proofFile(n, List(ObligationName.Complete, ObligationName.Impl))}",
      s"=== used by ${n.id} ===\n${(g.declarationsUsedBy(n) ++ g.sourcesUsedBy(n)).mkString("\n")}",
      s"=== not evaluated of ${n.id} ===\n${g.evals(n)._2.mkString("\n")}"))
    (files ++ perNode :+ s"=== lakefile ===\n${g.lakefile("../../lean")}").mkString("\n")

  private val fixtures: List[(String, KnowledgeBase)] = List(
    "shelf" -> shelfKb,
    // proven code calling another contract's operation: impl, root_impl, evaluated code
    "calls" -> callsKb)

  fixtures.foreach { (name, kb) =>
    test(s"the Lean of the $name fixture is as recorded") {
      val expected = scala.io.Source.fromResource(s"golden/$name.lean.txt")(using scala.io.Codec.UTF8).mkString
      val got = rendered(Generate(kb), kb)
      assertNoDiff(got, expected)
      assert(got == expected, "the same lines, but not the same bytes (whitespace at the ends of lines?)")
    }
  }
