import FrFlowGen.Keycloak.signedInAreAccepted.Spec
import Proofs.Keycloak.Lemmas

/-! A user signed in, and enabled, is accepted with their roles: their sign-in is a session the realm holds
(`sessionsMirrorSignIns`), the only one under its token (`oneSignInPerToken`, a rule of the store), of an account
enabled as administered (`accountsAsAdministered`); the introspection answers for such a session
(`introspectAnswers`), and what it answers is what is accepted (`referenceTokens`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.signedInAreAccepted.Proofs
open Keycloak

theorem complete : Obl.complete := by
  intro signedIn enabled accepted rolesOf introspect hEnabled hRoles hSigned hRef hMirror hAcc hIntro r t u w
    h1 h2 h3 hu
  obtain ⟨hs, he⟩ := hu
  rw [hSigned r u t w h1 h2 h3] at hs
  rw [hEnabled r u w h1 h2 h3, ← hAcc r u w h1 h2 h3] at he
  have hx : Session.mk t r u ∈ sessions w.serverStore.state r := by
    simp only [sessions, List.mem_filter, decide_eq_true_eq]
    rw [hMirror _ w h1 h2 h3]; exact ⟨hs, trivial⟩
  have hone : onlyOne (sessions w.serverStore.state r) (Session.mk t r u) := by
    intro y hy hyt
    simp only [sessions, List.mem_filter, decide_eq_true_eq] at hy
    rw [hMirror y w h1 h2 h3] at hy
    exact h2 y (Session.mk t r u) ⟨⟨hy.1, hs⟩, hyt⟩
  have hr := hRef r t w h1 h2 h3
  have hi := hIntro r t w h1 h2 h3
  revert hr hi
  generalize introspect r t w = p
  rcases p with ⟨res, aft⟩
  simp only
  intro hr hi
  have hans := hi.2 _ hx ⟨⟨⟨hx, rfl⟩, hone⟩, he⟩
  rw [hr, hans, hRoles r u w h1 h2 h3, ← hAcc r u w h1 h2 h3]
  rfl

/-- Some world meets the parts: the words as the server's store says them, an index answering from its sessions,
what is accepted what is answered. -/
theorem feasible : Obl.feasible := by
  obtain ⟨lookup, hO, hF, hK⟩ := Lemmas.some_index
  exact ⟨fun r u t w => liveIn w.serverStore.loaded w.serverStore.log (Session.mk t r u),
    fun r u w => isEnabled (accountOf (accountsAfter w.serverStore.loaded w.serverStore.log) r u),
    fun r t w => claimsOf (introspecting_run lookup r t w).1,
    fun r u w => rolesIn (accountOf (accountsAfter w.serverStore.loaded w.serverStore.log) r u),
    introspecting_run lookup, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
    Lemmas.reference (introspecting_run lookup), Lemmas.sessions_mirror, Lemmas.accounts_administered,
    Lemmas.introspect_answers lookup hO hF hK⟩

end Keycloak.signedInAreAccepted.Proofs
