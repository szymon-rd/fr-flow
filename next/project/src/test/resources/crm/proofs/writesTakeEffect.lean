import FrFlowGen.Crm.writesTakeEffect.Spec
import Proofs.Crm.Lemmas

/-! What a write asks takes effect (today's proof): the write leads to a store holding what was asked
(`writeContract`), and the write side stores that store's rows about the written record (`saveWrite`); what was
asked is about those rows only. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writesTakeEffect.Proofs
open Crm

theorem impl : Obl.impl := by
  intro storeRows write hWrite hSave s hk ho w
  have hSaved := hSave s hk ho w
  obtain ⟨⟨_, hTakes⟩, _⟩ := hWrite s hk ho w
  simp only [afterSave, saved] at hSaved ⊢
  rw [hSaved, Lemmas.aboutRecord_idem]
  exact Lemmas.takesEffect_replace s (write s w) w hTakes

end Crm.writesTakeEffect.Proofs
