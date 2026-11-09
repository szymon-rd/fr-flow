import FrFlowGen.Crm.jobReturnsExpired.Spec
import Proofs.Crm.Lemmas

/-! A run of the job (`Runs.expireOnce_run_eq`) returns the job's store. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.jobReturnsExpired.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro now world _ _ _
  rw [Runs.expireOnce_run_eq]

end Crm.jobReturnsExpired.Proofs
