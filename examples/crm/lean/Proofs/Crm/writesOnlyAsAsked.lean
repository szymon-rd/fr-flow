import FrFlowGen.Crm.writesOnlyAsAsked.Spec
import Proofs.Crm.Lemmas

/-! A write's code changes nothing it was not asked (`applyWrite_contract`), and what the write side holds is the store with its record's rows replaced by those (`onlyAsked_replace`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writesOnlyAsAsked.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun _ _ _ _ => Runs.writes_only_as_asked

end Crm.writesOnlyAsAsked.Proofs
