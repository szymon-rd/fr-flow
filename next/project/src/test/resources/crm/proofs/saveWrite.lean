import FrFlowGen.Crm.saveWrite.Spec
import Proofs.Crm.Lemmas

/-! The write side stores the rows the write's store has about its record: the database reads them back as stored
(`storeEdits`), of a store with one row per key, as a write keeps it (`applyWrite_onePerKey`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.saveWrite.Proofs
open Crm

theorem impl : Obl.impl := by
  intro storeRows hEdits s hk _ w
  have hw := Lemmas.applyWrite_onePerKey s w hk
  exact hEdits (about w) (applyWrite s w) hw hw

end Crm.saveWrite.Proofs
