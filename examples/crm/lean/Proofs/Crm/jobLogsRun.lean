import FrFlowGen.Crm.jobLogsRun.Spec
import Proofs.Crm.Lemmas

/-! A run of the job (`Runs.expireOnce_run_eq`) appends the run to the event log. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.jobLogsRun.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro _ _ _ _ _ now world _ _ _
  rw [Runs.expireOnce_run_eq]

end Crm.jobLogsRun.Proofs
