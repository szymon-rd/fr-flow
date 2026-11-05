import FrFlowGen.Crm.expiryJob.Spec
import Proofs.Crm.Lemmas

/-! A run of the job (`Runs.expireOnce_run_eq`): each record's rows the job's store changed stored again, so the database holds the same rows about every record as that store (`Runs.jobStored_sameRows`); the run logged at the end; that store given. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.expiryJob.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro now world _ _ _
  rw [Runs.expireOnce_run_eq]
  exact ⟨⟨Runs.jobStored_sameRows _ _, rfl⟩, rfl⟩

end Crm.expiryJob.Proofs
