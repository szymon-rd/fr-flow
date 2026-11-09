import FrFlowGen.Crm.writeContract.Spec
import Proofs.Crm.Lemmas

/-! A write leads to the store its author asked for: what its four parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeContract.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun h1 h2 h3 h4 s hk ho w =>
  ⟨⟨⟨h1 s hk ho w, h2 s hk ho w⟩, h3 s hk ho w⟩, h4 s hk ho w⟩

end Crm.writeContract.Proofs
