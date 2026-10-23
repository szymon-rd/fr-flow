package frflow
package lean

import frflow.protocol.{ObligationName, TryKind}

/** Reading Lean's output and source, on output recorded from Lean 4.35 (`lake env lean`, `lake build`). */
class LeanOutputSuite extends munit.FunSuite:

  private val source =
    """theorem good : 1 + 1 = 2 := by
      |  decide
      |
      |theorem bad : 1 + 1 = 3 := by
      |  decide
      |
      |theorem holey : 2 + 2 = 4 := by
      |  sorry
      |
      |#print axioms good
      |#print axioms holey
      |#print axioms Classical.em
      |""".stripMargin

  private val elaborated =
    """Proofs/Tmp.lean:5:2: error: Tactic `decide` proved that the proposition
      |  1 + 1 = 3
      |is false
      |Proofs/Tmp.lean:7:8: warning: declaration uses `sorry`
      |'good' does not depend on any axioms
      |'holey' depends on axioms: [sorryAx]
      |'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]
      |""".stripMargin

  private val built =
    """✖ [2/2] Building Proofs.Tmp (257ms)
      |trace: .> LEAN_PATH=… lean Proofs/Tmp.lean -o Proofs/Tmp.olean
      |error: Proofs/Tmp.lean:5:2: Tactic `decide` proved that the proposition
      |  1 + 1 = 3
      |is false
      |warning: Proofs/Tmp.lean:7:8: declaration uses `sorry`
      |info: Proofs/Tmp.lean:10:0: 'good' does not depend on any axioms
      |info: Proofs/Tmp.lean:11:0: 'holey' depends on axioms: [sorryAx]
      |info: Proofs/Tmp.lean:12:0: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]
      |Some required targets logged failures:
      |- Proofs.Tmp
      |error: build failed
      |""".stripMargin

  test("diagnostics, as `lean` prints them: a message goes on over the lines that follow it") {
    val ds = LeanOutput.diagnostics(elaborated)
    assertEquals(ds.map(d => (d.line, d.severity)), List((5, Severity.Error), (7, Severity.Warning)))
    assertEquals(ds.head.message, "Tactic `decide` proved that the proposition\n  1 + 1 = 3\nis false")
    assert(ds(1).isSorry && !ds(1).isError)
  }

  test("diagnostics, as `lake build` prints them: its own lines end a message") {
    val ds = LeanOutput.diagnostics(built)
    assertEquals(ds.map(d => (d.file, d.line, d.severity)), List(("Proofs/Tmp.lean", 5, Severity.Error), ("Proofs/Tmp.lean", 7, Severity.Warning),
      ("Proofs/Tmp.lean", 10, Severity.Info), ("Proofs/Tmp.lean", 11, Severity.Info), ("Proofs/Tmp.lean", 12, Severity.Info)))
    assertEquals(ds.last.message, "'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]")
  }

  test("the axioms each theorem rests on; Lean's short `choice` is Classical.choice") {
    val expected = Map("good" -> Nil, "holey" -> List("sorryAx"), "Classical.em" -> List("propext", "Classical.choice", "Quot.sound"))
    assertEquals(LeanOutput.axioms(elaborated), expected)
    assertEquals(LeanOutput.axioms(built), expected)
    assertEquals(LeanOutput.axioms("'X.holds' depends on axioms: [propext,\n choice]"), Map("X.holds" -> List("propext", "Classical.choice")))
    assert(LeanOutput.usesSorry(elaborated))
  }

  test("a theorem is proven when Lean reports no error within its lines and no sorry") {
    val e = Elaboration(source, elaborated, "Proofs/Tmp.lean")
    assertEquals(e.theorems.map(d => (d.name, d.statement, d.from, d.to)),
      List(("good", "1 + 1 = 2", 1, 3), ("bad", "1 + 1 = 3", 4, 6), ("holey", "2 + 2 = 4", 7, 9)))
    assertEquals(e.verdict("good"), TheoremVerdict.Proven)
    assertEquals(e.verdict("bad"), TheoremVerdict.Failed("Tactic `decide` proved that the proposition\n  1 + 1 = 3\nis false"))
    assertEquals(e.verdict("holey"), TheoremVerdict.UsesSorry)
    assertEquals(e.verdict("absent").why("absent"), Some("no theorem absent"))
    // what `#print axioms` printed after an error is not part of the error
    assertEquals(Elaboration(source, "Proofs/Tmp.lean:5:2: error: no\n'holey' depends on axioms: [sorryAx]\n", "Proofs/Tmp.lean").verdict("bad"),
      TheoremVerdict.Failed("no"))
    assertEquals(Elaboration(source, built, "Proofs/Tmp.lean").verdict("holey"), TheoremVerdict.UsesSorry)
    // what Lean says of another file says nothing of this one
    assertEquals(Elaboration(source, elaborated, "Proofs/Other.lean").verdict("bad"), TheoremVerdict.Proven)
  }

  test("sorry found among a theorem's axioms, without the warning") {
    val e = Elaboration(source, "'Tmp.holey' depends on axioms: [sorryAx]\n", "Proofs/Tmp.lean")
    assertEquals(e.verdict("holey"), TheoremVerdict.UsesSorry)
    assertEquals(e.axiomsOf("holey"), Some(List("sorryAx")))
  }

  test("comments and strings do not count as code, and keep their lines") {
    val src = "theorem a : True := by -- axiom\n  /- nested /- axiom -/ still -/ trivial\ndef s := \"axiom\\\"\" ++ 'x'.toString\n"
    val c = LeanSource.code(src)
    assertEquals(c.linesIterator.size, src.linesIterator.size)
    assertEquals(c.length, src.length)
    assert(!c.contains("axiom") && c.contains("trivial") && c.contains("toString"), c)
    assertEquals(LeanSource.theorems("-- theorem hidden : False := sorry\ntheorem shown : True := trivial\n").map(_.name), List("shown"))
  }

  test("what a proof file or the shared lemmas may not hold, in words") {
    assertEquals(ProofRules.notAllowed("theorem complete : Obl.complete := by\n  simp\n"), None)
    assertEquals(ProofRules.notAllowed("theorem t : True := by native_decide\naxiom bad : False\n"), Some("native_decide, command axiom, axiom"))
    assertEquals(ProofRules.notAllowedInLemmas("import Proofs.K.Lemmas\ntheorem t : True := trivial\n"), Some("import Proofs.K.Lemmas"))
    assertEquals(LeanSource.lemmaImports("import Proofs.K.Lemmas\nimport FrFlowGen.K.Domain\n"), List("Proofs.K.Lemmas"))
  }

  test("obligation names read back as written") {
    val names = List(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.Check, ObligationName.RootImpl,
      ObligationName.Cover("Isolated"), ObligationName.Expect(2), ObligationName.Eval(0), ObligationName.EvalImpl(3), ObligationName.Probe(1),
      ObligationName.ProbeImpl(5)) ++ List(TryKind.Needed("A_b"), TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle,
      TryKind.VacuousExpect(1)).map(ObligationName.Tried(_))
    assertEquals(names.map(n => ObligationName.parse(n.lean)), names.map(Some(_)))
    assertEquals(names.map(_.lean).take(7), List("complete", "feasible", "impl", "check", "root_impl", "cover_Isolated", "expect_2"))
    assertEquals(ObligationName.Tried(TryKind.VacuousExpect(1)).lean, "vacuous_expect_1")
    assertEquals(ObligationName.parse("holds"), None)
    assert(ObligationName.Probe(1).isEvaluation && ObligationName.Probe(1).isProbe && !ObligationName.Complete.isEvaluation)
  }
