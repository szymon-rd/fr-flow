import FrFlowGen.Crm.dealsOnlyReadable.Spec
import Proofs.Crm.Lemmas

/-! The sales screen returns only records the user may read now (`Runs.deal_search`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealsOnlyReadable.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.deals_only_readable fetch hO hA hK

end Crm.dealsOnlyReadable.Proofs
