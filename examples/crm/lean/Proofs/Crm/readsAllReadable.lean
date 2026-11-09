import FrFlowGen.Crm.readsAllReadable.Spec
import Proofs.Crm.Lemmas

/-! The records screen returns every stored record that matches and the user may read now: the database's search misses none (`Runs.read_contract`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.readsAllReadable.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun fetch hO hA hK => Runs.reads_all_readable fetch hO hA hK

end Crm.readsAllReadable.Proofs
