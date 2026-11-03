import FrFlowGen.Crm.writeContract.Spec
import Proofs.Crm.Lemmas

/-! The write's code keeps what writeContract says (`Lemmas.applyWrite_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeContract.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := applyWrite_contract

end Crm.writeContract.Proofs
