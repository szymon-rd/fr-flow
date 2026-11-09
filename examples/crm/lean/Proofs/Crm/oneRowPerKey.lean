import FrFlowGen.Crm.oneRowPerKey.Spec
import Proofs.Crm.Lemmas

/-! Every store the CRM makes and holds has one row per key: a write's (`applyWrite_onePerKey`), the rows the write side gives and leaves (`Runs.saved_onePerKey`), the job's store and what it leaves (`Runs.expired_onePerKey`); the screens change nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.oneRowPerKey.Proofs
open Crm Crm.Lemmas

theorem cover_read : Obl.cover_read := by
  intro fetch hO hA hK u q w h1 h2 h3
  have he := (Runs.searched fetch hO hA hK u q w ⟨h1, h2, h3⟩).1
  revert he
  generalize search_run fetch u q w = p
  rcases p with ⟨res, aft⟩
  intro he
  simp only at he ⊢
  rw [he]; exact h2

theorem cover_deals : Obl.cover_deals := by
  intro fetch hO hA hK u q w h1 h2 h3
  have he := (Runs.dealt fetch hO hA hK u q w ⟨h1, h2, h3⟩).1
  revert he
  generalize dealsOf_run fetch u q w = p
  rcases p with ⟨res, aft⟩
  intro he
  simp only at he ⊢
  rw [he]; exact h2

theorem cover_save : Obl.cover_save := by
  intro c w _ h2 _
  have he := Runs.saved_onePerKey c w h2
  revert he
  generalize saved_run c w = p
  rcases p with ⟨res, aft⟩
  exact id

theorem cover_runExpiry : Obl.cover_runExpiry := by
  intro now w _ h2 _
  have he := Runs.expired_onePerKey expireCode Runs.sharesExpire_code now w h2
  revert he
  generalize expireOnce_run expireCode now w = p
  rcases p with ⟨res, aft⟩
  exact id

theorem made_write : Obl.made_write := fun s hk _ c => applyWrite_onePerKey s c hk

theorem made_saved_call_1 : Obl.made_saved_call_1 := fun c s h => applyWrite_onePerKey s c h.1

/-- What the job hands the database to store is its expire's store, which keeps the rule (`m_expire`). -/
theorem made_expireOnce_call_1 : Obl.made_expireOnce_call_1 := by
  intro expire _ _ _ _ _ _ _ mX now s h _ _ _
  exact mX s h.1 h.2 now

theorem made_save : Obl.made_save := by
  intro c w _ h2 _
  rw [Runs.saved_run_eq]
  exact aboutRecord_onePerKey _ _ (applyWrite_onePerKey _ c h2)

theorem made_runExpiry : Obl.made_runExpiry := by
  intro expire _ _ _ _ _ _ _ mX now w _ h2 h3
  rw [Runs.expireOnce_run_eq]
  exact mX _ h2 h3 now

end Crm.oneRowPerKey.Proofs
