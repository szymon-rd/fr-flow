import FrFlowGen.Authz.T0.Obligations

/-!
Proofs of the obligations of node T0 (NoUnauthorizedAccess).

Authored file: write one `theorem <name> : Obl.<name>` per obligation.
The statement after the colon must be exactly `Obl.<name>`.
-/

namespace Authz.T0.Proofs
open Authz.T0

/-- Every initial state of T0 satisfies Safe. -/
theorem init_Safe : Obl.init_Safe := by
  intro s ⟨_, hlog⟩ e he
  simp [hlog] at he

/-- Event access preserves Safe. -/
theorem access_inv_Safe : Obl.access_inv_Safe := by
  intro s p hs ⟨_, hc⟩ e he
  simp only [access.act, List.mem_cons] at he
  rcases he with rfl | he
  · exact ⟨Nat.le_refl _, hc⟩
  · exact hs e he

/-- Event setPolicy preserves Safe: it only writes the new version, which no
logged entry refers to. -/
theorem setPolicy_inv_Safe : Obl.setPolicy_inv_Safe := by
  intro s p hs _ e he
  obtain ⟨hle, hp⟩ := hs e he
  refine ⟨Nat.le_succ_of_le hle, ?_⟩
  have hne : e.ver ≠ s.version + 1 := by omega
  show (if e.ver = s.version + 1 then p.pol else s.policy e.ver) e.user e.res e.act
  simp only [hne, ite_false]
  exact hp

end Authz.T0.Proofs
