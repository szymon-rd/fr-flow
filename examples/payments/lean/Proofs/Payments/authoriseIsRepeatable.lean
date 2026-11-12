import FrFlowGen.Payments.authoriseIsRepeatable.Spec
import Proofs.Payments.Lemmas

/-! The first call left the payment decided (`Lemmas.authorised_decided`); a payment decided is answered as it
was decided and nothing is changed (`Lemmas.decided_authorise`), and that answer is the first call's. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.authoriseIsRepeatable.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro limits p
  rw [decided_authorise _ p (authorised_decided limits p)]
  exact ⟨rfl, rfl⟩

end Payments.authoriseIsRepeatable.Proofs
