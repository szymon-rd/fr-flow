import FrFlowGen.Keycloak.answersOnlyEnabled.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection names only a user enabled in the realm: the index returns only a session the realm holds under the token (`lookupOnlyHeld`), and one whenever
the realm holds one (`lookupFindsHeld`), changing nothing the store holds (`lookupKeeps`); `Lemmas.only_enabled`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersOnlyEnabled.Proofs

theorem impl : Obl.impl := fun lookup hO hF hK => Keycloak.Lemmas.only_enabled lookup hO hF hK

end Keycloak.answersOnlyEnabled.Proofs
