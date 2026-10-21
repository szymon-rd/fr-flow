package frflow

import frflow.obligation.{ObligationKind, Obligations}

class ObligationsSuite extends munit.FunSuite:
  private val theory = CounterTheory.model

  test("root node: one init and one per-event obligation per invariant") {
    val obls = Obligations.forNode(theory, theory.nodeOrFail("C0"))
    assertEquals(obls.map(_.name), Seq("init_Le10", "inc_inv_Le10", "reset_inv_Le10"))
    assert(obls.forall(o => o.kind == ObligationKind.InitInvariant || o.kind == ObligationKind.EventInvariant))
  }

  test("refining node: glue, init_abs, guard and simulation per refined event, skip for new events") {
    val obls = Obligations.forNode(theory, theory.nodeOrFail("C1"))
    assertEquals(
      obls.map(_.name),
      Seq(
        "init_glue", "init_abs",
        "inc_inv_glue", "inc_grd", "inc_sim",
        "reset_inv_glue", "reset_grd", "reset_sim",
        "audit_inv_glue", "audit_skip"
      )
    )
  }

  test("guard obligation refers to the parent event through the witness") {
    val grd = Obligations.forNode(theory, theory.nodeOrFail("C1")).find(_.name == "inc_grd").get
    assertEquals(grd.statement, "∀ s p, Obl.Hyp s → inc.guard s p → C0.inc.guard (abs s) (inc.witness s p)")
  }

  test("skip obligation states that the abstract state is unchanged") {
    val skip = Obligations.forNode(theory, theory.nodeOrFail("C1")).find(_.name == "audit_skip").get
    assertEquals(skip.statement, "∀ s p, Obl.Hyp s → audit.guard s p → abs (audit.act s p) = abs s")
  }
