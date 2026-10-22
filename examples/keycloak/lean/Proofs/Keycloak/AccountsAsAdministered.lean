import FrFlowGen.Keycloak.AccountsAsAdministered.Spec

/-! Authored proof that the server holds the accounts as administered: a simulation (`FrFlow.simulates`)
whose abstraction is the accounts, since each request handled as HandleRequest says changes them as
`administer` does, from the accounts loaded at start. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.AccountsAsAdministered.Proofs
open Keycloak

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history step seed hStep
  simp only [Keycloak.HandleRequest.claim] at hStep
  have h := FrFlow.simulates (step := fun s q => step s q) (astep := administer) (α := ServerState.accounts)
    (init := ServerState.mk seed []) (ainit := seed) rfl (fun s e => (hStep s e).1.1.1) history
  intro r u
  simp only [Keycloak.account, Keycloak.stateAfter, Keycloak.accountsAfter]
  rw [h]

end Keycloak.AccountsAsAdministered.Proofs
