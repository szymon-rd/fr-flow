import FrFlowGen.Crm.writeOnlyAsked.Spec
import Proofs.Crm.Lemmas

/-! A write's code changes nothing it was not asked (`Lemmas.applyWrite_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeOnlyAsked.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun s hk ho w => (applyWrite_contract s hk ho w).2

end Crm.writeOnlyAsked.Proofs
