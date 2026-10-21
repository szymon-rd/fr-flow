import FrFlowGen.Authz.T1.Obligations

/-!
Proofs of the obligations of node T1 (AuthnThenAuthz).

Authored file: write one `theorem <name> : Obl.<name>` per obligation.
The statement after the colon must be exactly `Obl.<name>`.
-/

namespace Authz.T1.Proofs
open Authz.T1

/-- Under A1, the principal the implementation checks is the real requester. -/
theorem checked_is_actor {s : State} {p : access.Params} (g : access.guard s p) : p.u = p.actor :=
  g.1 _ g.2.1

/-- Every initial state of T1 maps to an initial state of T0. -/
theorem init_abs : Obl.init_abs := by
  intro s ⟨hv, hl, _⟩
  exact ⟨hv, hl⟩

/-- Whenever access is enabled in T1, T0.access is enabled for the witness parameters. -/
theorem access_grd : Obl.access_grd := by
  intro s p _ g
  refine ⟨trivial, ?_⟩
  show s.policy s.version p.actor p.r p.a
  rw [← checked_is_actor g]
  exact g.2.2

/-- The effect of access, seen through abs, is the effect of T0.access. -/
theorem access_sim : Obl.access_sim := by
  intro s p _ g
  simp [abs, access.act, T0.access.act, access.witness, checked_is_actor g]

/-- Event login does not change the state of T0 (it refines skip). -/
theorem login_skip : Obl.login_skip := by
  intro _ _ _ _
  rfl

/-- Event logout does not change the state of T0 (it refines skip). -/
theorem logout_skip : Obl.logout_skip := by
  intro _ _ _ _
  rfl

/-- Whenever setPolicy is enabled in T1, T0.setPolicy is enabled for the witness parameters. -/
theorem setPolicy_grd : Obl.setPolicy_grd := by
  intro _ _ _ _
  exact ⟨trivial, trivial⟩

/-- The effect of setPolicy, seen through abs, is the effect of T0.setPolicy. -/
theorem setPolicy_sim : Obl.setPolicy_sim := by
  intro _ _ _ _
  rfl

end Authz.T1.Proofs
