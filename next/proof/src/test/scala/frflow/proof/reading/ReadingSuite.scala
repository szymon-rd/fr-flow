package frflow.proof.reading

import frflow.core.name.NodeId
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.{ObligationName, TryKind}

/** Reading Lean's output and a file's theorems: messages with their continuation lines, the axioms audited, `sorry`,
  * each theorem's lines and verdict, and every obligation's name read back.
  */
class ReadingSuite extends munit.FunSuite:
  private val source = """import FrFlowGen.Crm.Domain
    |
    |namespace Crm.N.Checks
    |
    |theorem cover_book : Obl.cover_book := by
    |  frflow_auto
    |
    |theorem unsat : Obl.unsat := by
    |  frflow_auto
    |
    |theorem impl : Obl.impl := by
    |  sorry
    |
    |#print axioms Crm.N.Checks.cover_book
    |
    |end Crm.N.Checks
    |""".stripMargin
  private val output = """✔ [3/9] Built FrFlowGen.Crm.Types (1s)
    |✖ [8/9] Building FrFlowGen.Crm.N.Checks (2s)
    |error: FrFlowGen/Crm/N/Checks.lean:9:2: frflow_auto found no proof; prove this obligation in the node's proof file
    |⊢ False
    |warning: FrFlowGen/Crm/N/Checks.lean:11:8: declaration uses 'sorry'
    |info: FrFlowGen/Crm/N/Checks.lean:14:0: 'Crm.N.Checks.cover_book' depends on axioms: [propext,
    | choice, Quot.sound]
    |error: FrFlowGen/Crm/Other.lean:1:0: unknown identifier
    |error: build failed
    |""".stripMargin
  private val e = Elaboration(source, output, "FrFlowGen/Crm/N/Checks.lean")

  test("messages: Lake's and Lean's styles, continuation lines joined, other files' left out") {
    assertEquals(LeanOutput.diagnostics(output).map(d => (d.file, d.line, d.error)), List(
      ("FrFlowGen/Crm/N/Checks.lean", 9, true), ("FrFlowGen/Crm/N/Checks.lean", 11, false),
      ("FrFlowGen/Crm/N/Checks.lean", 14, false), ("FrFlowGen/Crm/Other.lean", 1, true)))
    assertEquals(LeanOutput.diagnostics(output).head.message.linesIterator.toList.last, "⊢ False")
    assertEquals(e.diagnostics.size, 3)
    assert(LeanOutput.usesSorry(output))
  }

  test("axioms: a wrapped list, `choice` read as Classical.choice") {
    assertEquals(e.axiomsOf("cover_book"), Some(List("propext", "Classical.choice", "Quot.sound")))
  }

  test("theorems: each from its head to the line before the next command, with its statement") {
    assertEquals(e.theorems, List(Theorem("cover_book", "Obl.cover_book", 5, 7), Theorem("unsat", "Obl.unsat", 8, 10),
      Theorem("impl", "Obl.impl", 11, 13)))
  }

  test("verdicts: proven, failed with Lean's errors, resting on sorry, missing") {
    assertEquals(e.verdict("cover_book"), TheoremVerdict.Proven)
    assert(e.verdict("unsat").isInstanceOf[TheoremVerdict.Failed])
    assertEquals(e.verdict("impl"), TheoremVerdict.UsesSorry)
    assertEquals(e.verdict("complete"), TheoremVerdict.Missing)
    val broken = Elaboration(source, "error: FrFlowGen/Crm/N/Checks.lean:1:0: unknown module", e.file)
    assert(broken.verdict("cover_book").isInstanceOf[TheoremVerdict.Failed], "an error before the first theorem")
  }

  test("every obligation's name reads back as the obligation") {
    val n = NodeId("Grants")
    val all = List(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.RootImpl,
      ObligationName.Cover("book"), ObligationName.Made("in_room"), ObligationName.Commute(2),
      ObligationName.Consistent(0), ObligationName.Start(n), ObligationName.Inhabited(n),
      ObligationName.Satisfiable(n, 0), ObligationName.Example(3)) ++ (List(TryKind.Needed(n), TryKind.Vacuous,
      TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle, TryKind.RestatesConjunct(n, 2))
      .map(ObligationName.Tried(_)))
    all.foreach(o => assertEquals(ObligationNames.read(LowerObligation.name(o).text), Some(o)))
    assertEquals(ObligationNames.read("helper"), None)
  }

  test("a proof file's theorems, by the obligations they prove") {
    assertEquals(ProofRules.theorems(ProofFile(NodeId("N"), source)),
      List(ObligationName.Cover("book"), ObligationName.Tried(TryKind.Unsat), ObligationName.Impl))
  }
