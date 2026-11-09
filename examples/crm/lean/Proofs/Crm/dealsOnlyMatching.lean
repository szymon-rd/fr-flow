import FrFlowGen.Crm.dealsOnlyMatching.Spec
import Proofs.Crm.Lemmas

/-! The sales screen returns only stored records that match (`Runs.deal_search`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealsOnlyMatching.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.deals_only_matching fetch hO hA hK

end Crm.dealsOnlyMatching.Proofs
