import FrFlowGen.Crm.saveStores.Spec
import Proofs.Crm.Lemmas

/-! The write side's run (`Runs.saved_run_eq`) holds the store the write leads to, its record's rows replaced. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.saveStores.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro c world _ _ _
  rw [Runs.saved_run_eq]

end Crm.saveStores.Proofs
