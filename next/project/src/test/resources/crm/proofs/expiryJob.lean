import FrFlowGen.Crm.expiryJob.Spec
import Proofs.Crm.Lemmas

/-! The expiry job's program, run on the database's model (today's proof, the loop now a branch per record, its
`ifM`): for each record either store mentions, the job stores the new store's rows about it when they differ from
the old (`loop`, `fold_world`); storing a record's rows changes what the database holds about that record only
(`about_replace`), so afterwards it holds the new store's rows about each record stored and its old rows about the
others (`about_stored`), which are the new store's too: equal where nothing was stored, or mentioned by neither
(`about_absent`). The run is logged last, and the program returns the new store. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.expiryJob.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro now w
  rcases w with ⟨⟨s, es⟩⟩
  intro _ _
  simp only [expireOnce_run, expireOnce, FrFlow.runOn_bind, FrFlow.runOn_pure, DatabaseModel.Ops.load_onWorld,
    DatabaseModel.Ops.storeAbout_onWorld, DatabaseModel.Ops.logEvent_onWorld, FrFlow.runOn_within,
    DatabaseModel.load, DatabaseModel.storeAbout, DatabaseModel.logEvent, FrFlow.runOn_get, FrFlow.runOn_set]
  rw [loop _ _ (fun x i => if ¬aboutRecord s i = aboutRecord (expireCode s now) i then World.mk (Tables.mk
      (replaceAbout x.databaseModel.store i (aboutRecord (expireCode s now) i)) x.databaseModel.events) else x) (by
    intro i x
    by_cases hc : ¬aboutRecord s i = aboutRecord (expireCode s now) i
    · simp only [hc, not_false_eq_true, ↓reduceIte, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
        FrFlow.runOn_get, FrFlow.runOn_set]
    · simp only [hc, ↓reduceIte, FrFlow.runOn_pure])]
  rw [fold_world _ (fun i => ¬aboutRecord s i = aboutRecord (expireCode s now) i)]
  refine ⟨⟨?_, rfl⟩, trivial⟩
  simp only [sameRows]
  intro j _
  rw [about_stored]
  split
  · rfl
  · rename_i hj
    by_cases hin : j ∈ idsIn s ++ idsIn (expireCode s now)
    · exact Classical.byContradiction fun hne => hj ⟨hin, hne⟩
    · simp only [List.mem_append, not_or] at hin
      rw [about_absent _ _ hin.1, about_absent _ _ hin.2]

end Crm.expiryJob.Proofs
