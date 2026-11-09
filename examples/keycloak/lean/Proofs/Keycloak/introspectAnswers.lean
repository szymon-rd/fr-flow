import FrFlowGen.Keycloak.introspectAnswers.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection answers as introspectAnswers says: its five parts, each proven of the introspection's program,
together (`Lemmas.answers_of_parts`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.introspectAnswers.Proofs

theorem impl : Obl.impl := fun _ hR hN hE hW hT _ _ _ =>
  Keycloak.Lemmas.answers_of_parts _ hR hN hE hW hT

end Keycloak.introspectAnswers.Proofs
