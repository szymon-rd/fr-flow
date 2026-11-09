import FrFlowGen.Keycloak.answersWithRoles.Spec
import Proofs.Keycloak.Lemmas

/-! An introspection gives the roles of the user's account in the realm: the index returns only a session the realm holds under the token (`lookupOnlyHeld`), and one whenever
the realm holds one (`lookupFindsHeld`), changing nothing the store holds (`lookupKeeps`); `Lemmas.with_roles`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersWithRoles.Proofs

theorem impl : Obl.impl := fun lookup hO hF hK => Keycloak.Lemmas.with_roles lookup hO hF hK

end Keycloak.answersWithRoles.Proofs
