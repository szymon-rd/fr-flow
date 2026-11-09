import FrFlowGen.Crm.readsOnlyMatching.Spec
import Proofs.Crm.Lemmas

/-! The records screen returns only stored records that match: what the database's search returns, filtered (`Runs.read_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.readsOnlyMatching.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.reads_only_matching fetch hO hA hK

end Crm.readsOnlyMatching.Proofs
