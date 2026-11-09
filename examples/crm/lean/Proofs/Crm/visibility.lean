import FrFlowGen.Crm.visibility.Spec
import Proofs.Crm.Lemmas

/-! A search on either screen returns exactly the stored records it asks for and the user may read now (`Runs.screened`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.visibility.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch _ _ hO hA hK => Runs.visible fetch hO hA hK

end Crm.visibility.Proofs
