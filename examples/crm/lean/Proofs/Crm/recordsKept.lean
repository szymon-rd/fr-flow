import FrFlowGen.Crm.recordsKept.Spec
import Proofs.Crm.Lemmas

/-! A write's code keeps every record (`applyWrite_contract`), so the write side's rows about its record keep the one there; the job's run keeps the records (`Runs.jobDone_mem`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.recordsKept.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun _ _ _ _ _ _ _ _ => Runs.records_kept

end Crm.recordsKept.Proofs
