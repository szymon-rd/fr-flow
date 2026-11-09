import FrFlowGen.Keycloak.answersTheSession.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection names the user of the one session the realm holds under the token, when
they are enabled: the index returns only a session the realm holds under the token (`lookupOnlyHeld`), and one whenever
the realm holds one (`lookupFindsHeld`), changing nothing the store holds (`lookupKeeps`); `Lemmas.the_session`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersTheSession.Proofs

theorem impl : Obl.impl := fun lookup hO hF hK => Keycloak.Lemmas.the_session lookup hO hF hK

end Keycloak.answersTheSession.Proofs
