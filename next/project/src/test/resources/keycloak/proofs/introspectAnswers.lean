import FrFlowGen.Keycloak.introspectAnswers.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection on the store's index (today's proof over the index's answer, `Lemmas.introspect_answers`): the
index changes nothing the store holds (`lookupKeeps`), so the introspection reads the accounts of the state the index
answered from; the index returns only a session the realm holds under the token (`sessionLookup`), so a claim names
such a session, its user enabled with their roles; and it returns one whenever the realm holds one under the token,
which, the token naming no other, is that one. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.introspectAnswers.Proofs

theorem impl : Obl.impl := fun lookup hS hK => Keycloak.Lemmas.introspect_answers lookup hS hK

end Keycloak.introspectAnswers.Proofs
