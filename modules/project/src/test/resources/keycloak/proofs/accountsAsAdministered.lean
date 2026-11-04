import FrFlowGen.Keycloak.accountsAsAdministered.Spec
import Proofs.Keycloak.Lemmas

/-! The server holds the accounts as administered (`Lemmas.accounts_administered`): its state is its requests handled
in turn by `next` (`serverRun`), which changes the accounts as `administer` does, from the accounts loaded at start. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.accountsAsAdministered.Proofs

theorem complete : Obl.complete := fun _ _ => Keycloak.Lemmas.accounts_administered

end Keycloak.accountsAsAdministered.Proofs
