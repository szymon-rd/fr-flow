import FrFlowGen.Keycloak.answersWhatItStores.Spec
import Proofs.Keycloak.Lemmas

/-! The server answers with the state it stores: storing a request reads back the state it is given
(`storeKeepsState`), the state the store then holds (`storeHoldsState`); `Lemmas.answers_stored`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersWhatItStores.Proofs

theorem impl : Obl.impl := fun nextRequest record hD hK hH hA hKL =>
  Keycloak.Lemmas.answers_stored nextRequest record hD hK hH hA hKL

end Keycloak.answersWhatItStores.Proofs
