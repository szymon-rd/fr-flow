import FrFlowGen.Crm.visibility.Spec

/-! A search returns exactly the stored records it asks for that the user may read: only stored records it asks
for, and every one the user may read (`searchesMatch`); each one the user may read, as the screens keep only those
(`search`, and `dealsOf` keeping its deals). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.visibility.Proofs
open Crm

theorem impl : Obl.impl := by
  intro held fetch clock hk ho hMatch _ _ u q r
  obtain ⟨hsub, hall⟩ := hMatch hk ho u q
  apply propext
  constructor
  · intro hr
    refine ⟨hsub r hr, ?_⟩
    rcases q with ⟨sc, se⟩
    cases sc with
    | Records =>
      simp only [results, search, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.2
    | Sales =>
      simp only [results, dealsOf, search, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.1.2
  · rintro ⟨⟨hs, ha⟩, hm⟩
    exact hall r hs ⟨ha, hm⟩

end Crm.visibility.Proofs
