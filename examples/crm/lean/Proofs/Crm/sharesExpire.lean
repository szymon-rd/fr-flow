import FrFlowGen.Crm.sharesExpire.Spec
import Proofs.Crm.Lemmas

/-! A run of the job ends exactly the shares whose time has come: what its three parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.sharesExpire.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun h1 h2 h3 s hk ho now =>
  ⟨⟨h1 s hk ho now, h2 s hk ho now⟩, h3 s hk ho now⟩

end Crm.sharesExpire.Proofs
