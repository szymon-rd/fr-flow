import FrFlowGen.Keycloak.sessionsMirrorSignIns.Spec
import Proofs.Keycloak.Lemmas

/-! The server's sessions mirror the sign-ins that still stand (`Lemmas.sessions_mirror`): its state is its
requests handled in turn by `next` (`serverRun`), each moving the sessions as handleRequest says of `next`, one more
request moving the sign-ins as `liveIn_snoc` says; no two sign-ins of the log share a token (`freshTokens`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.sessionsMirrorSignIns.Proofs

theorem complete : Obl.complete := fun _ _ => Keycloak.Lemmas.sessions_mirror

end Keycloak.sessionsMirrorSignIns.Proofs
