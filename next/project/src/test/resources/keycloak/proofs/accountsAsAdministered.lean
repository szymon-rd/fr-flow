import FrFlowGen.Keycloak.accountsAsAdministered.Spec

/-! The server holds the accounts as administered: its state is its requests handled in turn (`serverRun`), a
simulation (`FrFlow.simulates`) whose abstraction is the accounts, since each request handled as handleRequest says
changes them as `administer` does, from the accounts loaded at start. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.accountsAsAdministered.Proofs

theorem complete : Obl.complete := by
  intro history state seed step hRun hStep r u
  unfold serverRun.claim at hRun
  unfold handleRequest.claim at hStep
  have h := FrFlow.simulates (step := fun s q => step s q) (astep := administer) (α := ServerState.accounts)
    (init := ServerState.mk seed []) (ainit := seed) rfl (fun s e => (hStep s e).1.1.1) history
  rw [hRun]
  simp only [Keycloak.account, Keycloak.stateAfter, Keycloak.accountsAfter]
  rw [h]

end Keycloak.accountsAsAdministered.Proofs
