import FrFlowGen.Crm.dealSearch.Spec
import Proofs.Crm.Lemmas

/-! The sales screen on the database: the records screen's search, deals only; `Runs.dealt`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealSearch.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := Runs.deal_search

end Crm.dealSearch.Proofs
