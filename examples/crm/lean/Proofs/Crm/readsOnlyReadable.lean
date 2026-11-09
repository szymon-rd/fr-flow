import FrFlowGen.Crm.readsOnlyReadable.Spec
import Proofs.Crm.Lemmas

/-! The records screen returns only records the user may read now: it keeps only those (`Runs.read_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.readsOnlyReadable.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.reads_only_readable fetch hO hA hK

end Crm.readsOnlyReadable.Proofs
