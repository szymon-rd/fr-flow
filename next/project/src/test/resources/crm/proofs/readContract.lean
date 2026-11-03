import FrFlowGen.Crm.readContract.Spec
import Proofs.Crm.Lemmas

/-! The records screen on the database: what the database's search returns (`recordsByQuery`), the user's company's or shared with it at the clock's time, the search changing nothing (`searchKeeps`); `Runs.searched`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.readContract.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := Runs.read_contract

end Crm.readContract.Proofs
