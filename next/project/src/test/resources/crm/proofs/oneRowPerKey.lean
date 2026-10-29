import FrFlowGen.Crm.oneRowPerKey.Spec
import Proofs.Crm.Lemmas

/-! What the CRM makes holds one row per key (owner §40): a write adds a record only under an id no record has, and
replaces the one share, and the one time, of its record with its company (`applyWrite_onePerKey`); a run of the
expiry job stores, record by record, rows of a store with one row per key (`sharesExpire`: the same records, some
of the shares and expiries) over what the database held (`stored_onePerKey`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.oneRowPerKey.Proofs
open Crm Crm.Lemmas

theorem made_write : Obl.made_write := by
  intro s hk _ w
  exact applyWrite_onePerKey s w hk

theorem cover_runExpiry : Obl.cover_runExpiry := by
  intro expire held history save runExpiry _ _ _ _ hX _ now w
  rcases w with ⟨⟨s, es⟩⟩
  intro hk _
  have ht : onePerKey (expire s now) := endsDueAt_onePerKey s now _ (hX s hk hk now) hk
  simp only [expireOnce_run, expireOnce, FrFlow.runOn_bind, FrFlow.runOn_pure, DatabaseModel.Ops.load_onWorld,
    DatabaseModel.Ops.storeAbout_onWorld, DatabaseModel.Ops.logEvent_onWorld, FrFlow.runOn_within,
    DatabaseModel.load, DatabaseModel.storeAbout, DatabaseModel.logEvent, FrFlow.runOn_get, FrFlow.runOn_set]
  rw [loop _ _ (fun x i => if ¬aboutRecord s i = aboutRecord (expire s now) i then World.mk (Tables.mk
      (replaceAbout x.databaseModel.store i (aboutRecord (expire s now) i)) x.databaseModel.events) else x) (by
    intro i x
    by_cases hc : ¬aboutRecord s i = aboutRecord (expire s now) i
    · simp only [hc, not_false_eq_true, ↓reduceIte, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
        FrFlow.runOn_get, FrFlow.runOn_set]
    · simp only [hc, ↓reduceIte, FrFlow.runOn_pure])]
  rw [fold_world _ (fun i => ¬aboutRecord s i = aboutRecord (expire s now) i)]
  exact stored_onePerKey _ _ s (expire s now) hk ht

end Crm.oneRowPerKey.Proofs
