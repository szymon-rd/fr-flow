import FrFlowGen.Crm.dealsAllReadable.Spec
import Proofs.Crm.Lemmas

/-! The sales screen returns every stored deal that matches and the user may read now (`Runs.deal_search`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealsAllReadable.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.deals_all_readable fetch hO hA hK

end Crm.dealsAllReadable.Proofs
