import FrFlowGen.Keycloak.realmIsolation.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection names the realm asking: the index returns only a session the realm holds under the token (`lookupOnlyHeld`), and one whenever
the realm holds one (`lookupFindsHeld`), changing nothing the store holds (`lookupKeeps`); `Lemmas.isolated`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.realmIsolation.Proofs

theorem impl : Obl.impl := fun lookup hO hF hK => Keycloak.Lemmas.isolated lookup hO hF hK

end Keycloak.realmIsolation.Proofs
