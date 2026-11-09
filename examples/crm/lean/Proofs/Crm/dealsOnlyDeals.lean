import FrFlowGen.Crm.dealsOnlyDeals.Spec
import Proofs.Crm.Lemmas

/-! The sales screen keeps only deals (`Runs.deal_search`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealsOnlyDeals.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.deals_only_deals fetch hO hA hK

end Crm.dealsOnlyDeals.Proofs
