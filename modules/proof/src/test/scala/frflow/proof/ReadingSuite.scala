package frflow.proof

import frflow.proof.lean.print.Sentinel
import frflow.core.name.NodeId
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.*

/** Reading Lean's output and a file's theorems: messages with their continuation lines, the axioms audited, `sorry`,
  * each theorem's lines and verdict, and every obligation's name read back.
  */
class ReadingSuite extends munit.FunSuite:
  private val source = """import FrFlowGen.Crm.Domain
    |
    |namespace Crm.N.Checks
    |
    |theorem made_book : Obl.made_book := by
    |  frflow_auto
    |
    |theorem unsat : Obl.unsat := by
    |  frflow_auto
    |
    |theorem impl : Obl.impl := by
    |  sorry
    |
    |#print axioms Crm.N.Checks.made_book
    |
    |end Crm.N.Checks
    |""".stripMargin
  private val output = """✔ [3/9] Built FrFlowGen.Crm.Types (1s)
    |✖ [8/9] Building FrFlowGen.Crm.N.Checks (2s)
    |error: FrFlowGen/Crm/N/Checks.lean:9:2: frflow_auto found no proof; prove this obligation in the node's proof file
    |⊢ False
    |warning: FrFlowGen/Crm/N/Checks.lean:11:8: declaration uses 'sorry'
    |info: FrFlowGen/Crm/N/Checks.lean:14:0: 'Crm.N.Checks.made_book' depends on axioms: [propext,
    | choice, Quot.sound]
    |error: FrFlowGen/Crm/Other.lean:1:0: unknown identifier
    |info: FrFlowGen/Crm/M/Checks.lean:9:0: 'Crm.M.Checks.made_book' depends on axioms: [sorryAx]
    |error: build failed
    |""".stripMargin
  private val e = Elaboration(source, output, "FrFlowGen/Crm/N/Checks.lean")

  test("messages: Lake's and Lean's styles, continuation lines joined, other files' left out") {
    assertEquals(LeanOutput.diagnostics(output).map(d => (d.file, d.line, d.error)), List(
      ("FrFlowGen/Crm/N/Checks.lean", 9, true), ("FrFlowGen/Crm/N/Checks.lean", 11, false),
      ("FrFlowGen/Crm/N/Checks.lean", 14, false), ("FrFlowGen/Crm/Other.lean", 1, true),
      ("FrFlowGen/Crm/M/Checks.lean", 9, false)))
    assertEquals(LeanOutput.diagnostics(output).head.message.linesIterator.toList.last, "⊢ False")
    assertEquals(e.diagnostics.size, 3)
    assert(LeanOutput.usesSorry(output))
  }

  test("axioms: a wrapped list, `choice` read as Classical.choice; another file's audit of the name not this one's") {
    assertEquals(e.axiomsOf("made_book"), Some(List("propext", "Classical.choice", "Quot.sound")))
    assertEquals(e.verdict("made_book"), TheoremVerdict.Proven)
  }

  test("theorems: each from its head to the line before the next command, with its statement") {
    assertEquals(e.theorems, List(Theorem("made_book", "Obl.made_book", 5, 7), Theorem("unsat", "Obl.unsat", 8, 10),
      Theorem("impl", "Obl.impl", 11, 13)))
  }

  test("verdicts: proven, failed with Lean's errors, resting on sorry, missing") {
    assertEquals(e.verdict("made_book"), TheoremVerdict.Proven)
    assert(e.verdict("unsat").isInstanceOf[TheoremVerdict.Failed])
    assertEquals(e.verdict("impl"), TheoremVerdict.UsesSorry)
    assertEquals(e.verdict("complete"), TheoremVerdict.Missing)
    val broken = Elaboration(source, "error: FrFlowGen/Crm/N/Checks.lean:1:0: unknown module", e.file)
    assert(broken.verdict("made_book").isInstanceOf[TheoremVerdict.Failed], "an error before the first theorem")
  }

  test("a theorem after where Lean stopped, having reported as many errors as it reports, is not proven") {
    val stopped = Elaboration(source, "error: FrFlowGen/Crm/N/Checks.lean:8:2: maximum number of errors (100; from " +
      "option `maxErrors`) reached, exiting\n", e.file)
    assertEquals(stopped.stopped, Some(8))
    assertEquals(List("made_book", "unsat").map(stopped.verdict), List(TheoremVerdict.Proven, TheoremVerdict.Missing))
  }

  test("a file FrFlow wrote whose last line Lean did not print was cut off: nothing in it is proven or shown") {
    val written = source + Sentinel.line("FrFlowGen.Crm.N.Checks") + "\n"
    val ended = output + "info: FrFlowGen/Crm/N/Checks.lean:18:0: frflow-end FrFlowGen.Crm.N.Checks\n"
    val (cut, whole) = (Elaboration(written, output, e.file), Elaboration(written, ended, e.file))
    assertEquals((cut.stopped, whole.stopped), (Some(0), None))
    assertEquals(List("made_book", "unsat", "impl").map(cut.verdict), List.fill(3)(TheoremVerdict.Missing))
    assertEquals(whole.verdict("made_book"), TheoremVerdict.Proven)
    assertEquals(Sentinel.of(written), Some("frflow-end FrFlowGen.Crm.N.Checks"))
    assertEquals((Sentinel.of(source), e.stopped), (None, None))
  }

  test("a dependency's last line, printed in the same build, is not this file's: it still reads as cut off") {
    val written = source + Sentinel.line("FrFlowGen.Crm.N") + "\n"
    val file = "FrFlowGen/Crm/N.lean"
    val dependency = "info: FrFlowGen/Crm/N/Checks.lean:18:0: frflow-end FrFlowGen.Crm.N.Checks\n"
    val own = s"info: $file:18:0: frflow-end FrFlowGen.Crm.N\n"
    assertEquals(Elaboration(written, dependency, file).stopped, Some(0))
    assertEquals(Elaboration(written, s"info: $file:3:0: frflow-end FrFlowGen.Crm.N.Checks\n", file).stopped, Some(0))
    assertEquals(Elaboration(written, dependency + own, file).stopped, None)
    // Lake's next line, which its messages do not end before, is no part of the line Lean printed.
    assertEquals(Elaboration(written, own + "ℹ [24/29] Built FrFlowGen.Crm.Whole (1.7s)\n", file).stopped, None)
  }

  test("every obligation's name reads back as the obligation") {
    val n = NodeId("Grants")
    val all = List(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.RootImpl,
      ObligationName.Made("in_room"), ObligationName.Consistent(0), ObligationName.Inhabited(n),
      ObligationName.Satisfiable(n, 0), ObligationName.Example("GrantedExamples", 3),
      ObligationName.ExampleOpposite("GrantedExamples", 3)) ++ (List(TryKind.Needed(n),
      TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle, TryKind.RestatesConjunct(n, 2))
      .map(ObligationName.Tried(_)))
    all.foreach(o => assertEquals(ObligationNames.read(LowerObligation.name(o).text), Some(o)))
    assertEquals(ObligationNames.read("helper"), None)
  }

  test("a proof file's theorems, by the obligations they prove") {
    assertEquals(ProofRules.theorems(ProofFile(NodeId("N"), source)),
      List(ObligationName.Made("book"), ObligationName.Tried(TryKind.Unsat), ObligationName.Impl))
  }
