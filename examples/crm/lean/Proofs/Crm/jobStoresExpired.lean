import FrFlowGen.Crm.jobStoresExpired.Spec
import Proofs.Crm.Lemmas

/-! A run of the job (`Runs.expireOnce_run_eq`) stores again each record's rows the job's store changed, so the database holds the same rows about every record as that store (`Runs.jobStored_sameRows`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.jobStoresExpired.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro now world _ _ _
  rw [Runs.expireOnce_run_eq]
  exact Runs.jobStored_sameRows _ _

end Crm.jobStoresExpired.Proofs
