import FrFlowGen.Crm.writeKeepsOthers.Spec
import Proofs.Crm.Lemmas

/-! A write's code leaves the records of other companies as they were (`Lemmas.applyWrite_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeKeepsOthers.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun s hk ho w => (applyWrite_contract s hk ho w).1.1.2

end Crm.writeKeepsOthers.Proofs
