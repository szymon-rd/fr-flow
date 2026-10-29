import FrFlowGen.Crm.writesOnlyAsAsked.Spec
import Proofs.Crm.Lemmas

/-! A write changes nothing it did not ask (today's proof): the write leads to a store that changes nothing it did
not ask (`writeContract`), and the write side stores only that store's rows about the written record
(`saveWrite`): every other row is the one the database held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writesOnlyAsAsked.Proofs
open Crm

theorem impl : Obl.impl := by
  intro storeRows write hWrite hSave s hk ho w
  have hSaved := hSave s hk ho w
  obtain ⟨_, hOnly⟩ := hWrite s hk ho w
  simp only [afterSave, saved] at hSaved ⊢
  rw [hSaved, Lemmas.aboutRecord_idem]
  exact Lemmas.onlyAsked_replace s (write s w) w hOnly

end Crm.writesOnlyAsAsked.Proofs
