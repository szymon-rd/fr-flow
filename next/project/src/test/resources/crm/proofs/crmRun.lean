import FrFlowGen.Crm.crmRun.Spec
import Proofs.Crm.Lemmas

/-! What the database holds is what its history led to, kept by every program changing it: the screens change nothing (`searchKeeps`, `Runs.searched`), the write side stores what one more write leads to and logs it (`Runs.saved_crmRun`), the job what one more run leads to (`Runs.expired_crmRun`, the job run as sharesExpire says being its code). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.crmRun.Proofs
open Crm Crm.Lemmas

theorem cover_read : Obl.cover_read := by
  intro fetch hR hK u q w h1 h2 h3
  have he := (Runs.searched fetch hR hK u q w ⟨h1, h2, h3⟩).1
  revert he
  generalize search_run fetch u q w = p
  rcases p with ⟨res, aft⟩
  intro he
  simp only at he ⊢
  rw [he]; exact h1

theorem cover_deals : Obl.cover_deals := by
  intro fetch hR hK u q w h1 h2 h3
  have he := (Runs.dealt fetch hR hK u q w ⟨h1, h2, h3⟩).1
  revert he
  generalize dealsOf_run fetch u q w = p
  rcases p with ⟨res, aft⟩
  intro he
  simp only at he ⊢
  rw [he]; exact h1

theorem cover_save : Obl.cover_save := by
  intro c w h1 _ _
  have he := Runs.saved_crmRun c w h1
  revert he
  generalize saved_run c w = p
  rcases p with ⟨res, aft⟩
  exact id

theorem cover_runExpiry : Obl.cover_runExpiry := by
  intro expire hX _ now w h1 h2 h3
  have he := Runs.expired_crmRun expire hX now w ⟨h1, h2, h3⟩
  revert he
  generalize expireOnce_run expire now w = p
  rcases p with ⟨res, aft⟩
  exact id

end Crm.crmRun.Proofs
