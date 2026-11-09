import FrFlowGen.Crm.saveReturns.Spec
import Proofs.Crm.Lemmas

/-! The write side's run (`Runs.saved_run_eq`) returns the rows the write leads to about its record, which are what the database then holds about it (`about_replace`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.saveReturns.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro c world _ _ _
  rw [Runs.saved_run_eq]
  simp only [afterSave, about_replace, ite_true]

end Crm.saveReturns.Proofs
