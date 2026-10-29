import FrFlowGen.Crm.recordsKept.Spec
import Proofs.Crm.Lemmas

/-! No write and no run of the expiry job removes a record: a write keeps every record (`writeContract`) and the
write side stores the written record's rows of that store (`saveWrite`), the others kept; a run keeps the records
as they were (`sharesExpire`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.recordsKept.Proofs
open Crm

theorem impl : Obl.impl := by
  intro storeRows write hWrite hSave hExpire s hk ho e r hr
  cases e with
  | Wrote w =>
    have hSaved := hSave s hk ho w
    obtain ⟨⟨⟨hKeeps, _⟩, _⟩, _⟩ := hWrite s hk ho w
    simp only [stepOf, afterSave, saved] at hSaved ⊢
    rw [hSaved, Lemmas.mem_records]
    by_cases hid : r.id_ = about w
    · exact Or.inr ⟨hKeeps r hr, hid⟩
    · exact Or.inl ⟨hr, hid⟩
  | Expired now =>
    simp only [stepOf]
    obtain ⟨⟨hRecords, _⟩, _⟩ := hExpire s hk ho now
    rw [hRecords]
    exact hr

end Crm.recordsKept.Proofs
