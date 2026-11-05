import FrFlowGen.Crm.saveWrite.Spec
import Proofs.Crm.Lemmas

/-! The write side's run (`Runs.saved_run_eq`): the rows the write leads to about its record held in place of the database's, the write logged, those rows given, which are what the database then holds about it (`about_replace`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.saveWrite.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro c world _ _ _
  rw [Runs.saved_run_eq]
  refine ⟨rfl, ?_⟩
  simp only [afterSave, about_replace, ite_true]

end Crm.saveWrite.Proofs
