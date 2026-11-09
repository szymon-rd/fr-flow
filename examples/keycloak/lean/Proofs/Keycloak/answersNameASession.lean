import FrFlowGen.Keycloak.answersNameASession.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection answers only with a session the realm holds under the token: the index returns only a session the realm holds under the token (`lookupOnlyHeld`), and one whenever
the realm holds one (`lookupFindsHeld`), changing nothing the store holds (`lookupKeeps`); `Lemmas.names_session`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersNameASession.Proofs

theorem impl : Obl.impl := fun lookup hO hF hK => Keycloak.Lemmas.names_session lookup hO hF hK

end Keycloak.answersNameASession.Proofs
