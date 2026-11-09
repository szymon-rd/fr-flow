import FrFlowGen.Keycloak.onlyTheSignedIn.Spec
import Proofs.Keycloak.Lemmas

/-! A token is accepted only as a user signed in with it: what is accepted is what the introspection answers
(`referenceTokens`), which names a session the asking realm holds under the token (`answersNameASession`,
`realmIsolation`); the server holds a session exactly when its sign-in still stands (`sessionsMirrorSignIns`),
which is being signed in (`signInHistory`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.onlyTheSignedIn.Proofs
open Keycloak

theorem complete : Obl.complete := by
  intro accepted signedIn introspect hSigned hRef hIso hAns hMirror r t w h1 h2 h3 a ha
  have hr := hRef r t w h1 h2 h3
  have hi := hIso r t w h1 h2 h3
  have hn := hAns r t w h1 h2 h3
  revert hr hi hn
  generalize introspect r t w = p
  rcases p with ⟨res, aft⟩
  simp only
  intro hr hi hn
  rw [hr] at ha
  cases res with
  | none => simp [claimsOf] at ha
  | some c =>
    simp only [claimsOf, Option.some.injEq] at ha
    subst ha
    have hcr : c.realm = r := hi c rfl
    have hx := hn c rfl
    simp only [Keycloak.sessions, List.mem_filter, decide_eq_true_eq] at hx
    rw [hMirror _ w h1 h2 h3] at hx
    rw [hSigned r c.user t w h1 h2 h3, ← hcr]
    exact hx.1

/-- Some world meets the parts: an introspection answering nothing, nothing accepted; the server's sessions
mirroring the sign-ins, as its code keeps them. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun _ _ _ => none, fun r u t w => liveIn w.serverStore.loaded w.serverStore.log (Session.mk t r u),
    fun _ _ w => (none, w), fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_, ?_,
    Lemmas.sessions_mirror⟩
  all_goals
    intro _ _ _ _ _ _ c hc
    cases hc

end Keycloak.onlyTheSignedIn.Proofs
