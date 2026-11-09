import FrFlowGen.Crm.saveLogs.Spec
import Proofs.Crm.Lemmas

/-! The write side's run (`Runs.saved_run_eq`) appends the write to the event log. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.saveLogs.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro c world _ _ _
  rw [Runs.saved_run_eq]

end Crm.saveLogs.Proofs
