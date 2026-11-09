import FrFlowGen.Crm.storeMirrorsRequests.Spec
import Proofs.Crm.Lemmas

/-! What the CRM holds is what its users asked: what its two parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.storeMirrorsRequests.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun hA hS world h1 h2 h3 =>
  ⟨fun r => hA r world h1 h2 h3, fun i c => hS i c world h1 h2 h3⟩

end Crm.storeMirrorsRequests.Proofs
