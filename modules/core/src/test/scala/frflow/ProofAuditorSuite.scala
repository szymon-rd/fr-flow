package frflow

import frflow.check.{Diagnostics, ProofAuditor}

class ProofAuditorSuite extends munit.FunSuite:

  private val src =
    """import X
      |
      |/-- doc mentioning axiom and sorry -/
      |theorem a : Obl.a := by
      |  -- a comment with admit
      |  simp
      |
      |/- block /- nested -/ axiom -/
      |theorem b : Obl.b :=
      |  trivial
      |axiom cheat : False
      |theorem c : True := "admit".length.succ_ne_zero.elim
      |end X
      |""".stripMargin

  test("comment and string stripping preserves line structure") {
    val stripped = ProofAuditor.stripComments(src)
    assertEquals(stripped.linesIterator.size, src.linesIterator.size)
    assert(!stripped.contains("nested"))
    assert(!stripped.contains("admit"))
  }

  test("only code outside comments and strings is flagged") {
    assertEquals(ProofAuditor.violations(src).map(v => v.line -> v.what), Seq(11 -> "axiom"))
  }

  test("declarations carry name, statement and a range ending at the next command") {
    val ds = ProofAuditor.declarations(src).map(d => (d.name, d.statement, d.startLine, d.endLine))
    assertEquals(ds, Seq(("a", "Obl.a", 4, 8), ("b", "Obl.b", 9, 10), ("c", "True", 12, 12)))
  }

  test("diagnostics: lean and lake formats, continuation lines, sorry") {
    val out =
      """✖ [3/4] Building Proofs.X
        |error: Proofs/X.lean:12:4: unsolved goals
        |s : State
        |⊢ False
        |Proofs/X.lean:20:0: warning: declaration uses `sorry`
        |Build completed successfully.
        |""".stripMargin
    val ds = Diagnostics.parse(out)
    assertEquals(ds.map(d => (d.file, d.line, d.severity)), Seq(("Proofs/X.lean", 12, "error"), ("Proofs/X.lean", 20, "warning")))
    assert(ds.head.message.contains("⊢ False"))
    assert(ds(1).isSorry)
  }

  test("axiom audit output") {
    val out =
      """'A.T1.refinement' depends on axioms: [propext, Quot.sound]
        |'A.T0.invariant' does not depend on any axioms
        |""".stripMargin
    assertEquals(
      Diagnostics.parseAxioms(out),
      Map("A.T1.refinement" -> Set("propext", "Quot.sound"), "A.T0.invariant" -> Set.empty[String])
    )
  }
