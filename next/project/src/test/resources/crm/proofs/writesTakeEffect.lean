import FrFlowGen.Crm.writesTakeEffect.Spec
import Proofs.Crm.Lemmas

/-! A write's code does what was asked (`applyWrite_contract`), and what the write side holds about the written record is what it leads to (`takesEffect_replace`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writesTakeEffect.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun _ _ _ _ => Runs.writes_take_effect

end Crm.writesTakeEffect.Proofs
