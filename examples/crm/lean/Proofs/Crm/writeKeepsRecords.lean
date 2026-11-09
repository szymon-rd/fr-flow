import FrFlowGen.Crm.writeKeepsRecords.Spec
import Proofs.Crm.Lemmas

/-! A write's code keeps every record (`Lemmas.applyWrite_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeKeepsRecords.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun s hk ho w => (applyWrite_contract s hk ho w).1.1.1

end Crm.writeKeepsRecords.Proofs
