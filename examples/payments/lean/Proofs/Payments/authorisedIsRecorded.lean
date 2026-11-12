import FrFlowGen.Payments.authorisedIsRecorded.Spec
import Proofs.Payments.Lemmas

/-! The answer is read from the decisions once the payment is decided, so it is the decision recorded; and the
payment is decided (`Lemmas.authorised_decided`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.authorisedIsRecorded.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := fun limits p => ⟨authorised_decided limits p, rfl⟩

end Payments.authorisedIsRecorded.Proofs
