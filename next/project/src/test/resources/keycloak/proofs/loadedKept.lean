import FrFlowGen.Keycloak.loadedKept.Spec
import Proofs.Keycloak.Lemmas

/-! The accounts as loaded are kept by every program changing the store: the server's stores them again
(`storeLogs`), an introspection changes nothing (`lookupKeeps`); `Lemmas.loaded_kept`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.loadedKept.Proofs

theorem impl : Obl.impl := fun nextRequest record lookup hD hK hL _ hLk =>
  Keycloak.Lemmas.loaded_kept nextRequest record lookup hD hK hL hLk

end Keycloak.loadedKept.Proofs
