import FrFlowGen.Crm.expiryKeepsLiveTimes.Spec
import Proofs.Crm.Lemmas

/-! The job's code (`expireCode`) is the store with the shares not ended and their times, and the same records. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.expiryKeepsLiveTimes.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := fun _ _ _ _ => rfl

end Crm.expiryKeepsLiveTimes.Proofs
