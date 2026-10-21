package frflow

import frflow.dsl.*
import frflow.model.*

/** A small two-node theory: a bounded counter refined by a counter with a cap register. */
object CounterTheory extends TheoryDef("Counter"):
  vocabulary(typeAlias("Cap", "Nat", "Maximum value of the counter."))

  val Env = assumption("E1", "CapPositive", "The configured cap is positive.", "Set by deployment configuration.")

  val C0 = root("C0", "Bounded", "The counter never exceeds 10.", "Simplest bounded resource.")(
    NodeSpec(
      state = Seq(field("n", "Nat")),
      init = lean("s.n = 0"),
      events = Seq(
        event("inc").check("s.n < 10").act("{ s with n := s.n + 1 }"),
        event("reset").act("{ s with n := 0 }")
      ),
      invariants = Seq(invariant("Le10", "s.n ≤ 10"))
    )
  )

  val C1 = C0.refine("C1", "CapRegister", "The counter stays below a configured cap of at most 10.", "Makes the bound configurable.")(
    link = link(abs = "{ n := s.n }", glue = "s.cap ≤ 10"),
    spec = NodeSpec(
      state = Seq(field("n", "Nat"), field("cap", "Cap")),
      init = lean("s.n = 0 ∧ s.cap ≤ 10"),
      events = Seq(
        event("inc").assume(Env, "0 < s.cap").check("s.n < s.cap").act("{ s with n := s.n + 1 }").refines("inc", "{}"),
        event("reset").act("{ s with n := 0 }").refines("reset", "{}"),
        event("audit").refinesSkip
      )
    )
  )
