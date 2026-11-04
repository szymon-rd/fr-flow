import FrFlowGen.Keycloak.rolesAsGranted.Spec
import Proofs.Keycloak.Lemmas

/-! A token is accepted only with the roles the realm gives its user: what is accepted is what the introspection
answers (`referenceTokens`), with the roles of the account the server holds (`introspectAnswers`), the account as
administered (`accountsAsAdministered`), whose roles are the user's (`accountRoles`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.rolesAsGranted.Proofs
open Keycloak

theorem complete : Obl.complete := by
  intro accepted rolesOf introspect hRoles hRef hAcc hIntro r t w h1 h2 h3 a ha
  have hr := hRef r t w h1 h2 h3
  have hi := hIntro r t w h1 h2 h3
  revert hr hi
  generalize introspect r t w = p
  rcases p with ⟨res, aft⟩
  simp only
  intro hr hi
  rw [hr] at ha
  cases res with
  | none => simp [claimsOf] at ha
  | some c =>
    simp only [claimsOf, Option.some.injEq] at ha
    subst ha
    rw [hRoles r c.user w h1 h2 h3, ← hAcc r c.user w h1 h2 h3]
    exact (hi.1 c rfl).2

/-- Some world meets the parts: an index answering from the store's sessions, what is accepted what is answered. -/
theorem feasible : Obl.feasible := by
  obtain ⟨lookup, hS, hK⟩ := Lemmas.some_index
  exact ⟨fun r t w => claimsOf (introspecting_run lookup r t w).1,
    fun r u w => rolesIn (accountOf (accountsAfter w.serverStore.loaded w.serverStore.log) r u),
    introspecting_run lookup, fun _ _ _ _ _ _ => rfl, Lemmas.reference (introspecting_run lookup),
    Lemmas.accounts_administered, Lemmas.introspect_answers lookup hS hK⟩

end Keycloak.rolesAsGranted.Proofs
