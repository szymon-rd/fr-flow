package frflow

import frflow.render.{Guarantee, LeanRenderer}

class LeanRendererSuite extends munit.FunSuite:
  private val theory = CounterTheory.model
  private val r = LeanRenderer(theory)

  test("conjunctions parenthesize compound clauses and default to True") {
    assertEquals(LeanRenderer.conj(Nil), "True")
    assertEquals(LeanRenderer.conj(Seq("a")), "a")
    assertEquals(LeanRenderer.conj(Seq("s.n < 10", "ok")), "(s.n < 10) ∧ ok")
  }

  test("tuples and projections agree on right-nested conjunctions") {
    assertEquals(LeanRenderer.tuple(Nil), "trivial")
    assertEquals(LeanRenderer.tuple(Seq("x")), "x")
    assertEquals(LeanRenderer.tuple(Seq("x", "y", "z")), "⟨x, y, z⟩")
    assertEquals(LeanRenderer.projection(0, 1), "")
    assertEquals(LeanRenderer.projection(0, 3), ".1")
    assertEquals(LeanRenderer.projection(1, 3), ".2.1")
    assertEquals(LeanRenderer.projection(2, 3), ".2.2")
  }

  test("list membership proofs follow the event index") {
    assertEquals(LeanRenderer.memPath(0), "(List.Mem.head _)")
    assertEquals(LeanRenderer.memPath(2), "(List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))")
  }

  test("model lists events in declaration order and renders the link") {
    val model = r.renderModel(theory.nodeOrFail("C1"))
    assert(model.contains("def machine : FrFlow.Machine := ⟨State, Init, [inc.event, reset.event, audit.event]⟩"))
    assert(model.contains("def abs (s : State) : C0.State := { n := s.n }"))
    assert(model.contains("def glue (s : State) : Prop := s.cap ≤ 10"))
    assert(model.contains("def inc.assume (s : State) (p : inc.Params) : Prop := (0 < s.cap)"))
    assert(model.contains("def audit.act (s : State) (p : audit.Params) : State := s"))
  }

  test("assembly uses the parent event index for membership") {
    val asm = r.renderAssembly(theory.nodeOrFail("C1"))
    assert(asm.contains("EventSim.refines C0.reset.event (List.Mem.tail _ (List.Mem.head _)) reset.witness"), asm)
    assert(asm.contains("EventSim.skip (fun s p h g => Proofs.audit_inv_glue s p h g) Proofs.audit_skip"), asm)
  }

  test("guarantees: own invariants and inherited ones with the abstraction chain") {
    val gs = r.guarantees(theory.nodeOrFail("C1"))
    assertEquals(gs, Seq(Guarantee("C0", "Le10", List("C1"))))
    assertEquals(gs.head.theoremName, "C1.inherits_C0_Le10")
    assertEquals(gs.head.predicate, "fun s => C0.Le10 (C1.abs (s))")
    assertEquals(r.auditedTheorems(theory.nodeOrFail("C1")), Seq("Counter.C1.refinement", "Counter.C1.inherits_C0_Le10"))
  }

  test("user text cannot close a Lean comment") {
    assertEquals(LeanRenderer.wrapComment("a -/ b"), "a - / b")
  }
