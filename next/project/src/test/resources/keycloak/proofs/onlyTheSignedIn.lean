import FrFlowGen.Keycloak.onlyTheSignedIn.Spec

/-! A token is accepted only as the user who signed in with it: what is accepted is what the introspection answers
(`referenceTokens`), which names a session the realm asking holds (`answersNameASession`, `realmIsolation`), and a
session held is a sign-in that still stands (`sessionsMirrorSignIns`, `signInHistory`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.onlyTheSignedIn.Proofs

theorem complete : Obl.complete := by
  intro accepted signedIn history seed introspect state hSigned hRef hIso hAns hMirror r t a ha
  unfold signInHistory.claim at hSigned
  unfold referenceTokens.claim at hRef
  unfold realmIsolation.claim at hIso
  unfold answersNameASession.claim at hAns
  unfold sessionsMirrorSignIns.claim at hMirror
  rw [hRef] at ha
  cases hc : introspect r t with
  | none => simp [hc, claimsOf] at ha
  | some c =>
    simp only [hc, claimsOf, Option.some.injEq] at ha
    subst ha
    have hr : c.realm = r := hIso r t c hc
    have hx := hAns r t c hc
    rw [hMirror] at hx
    rw [hSigned, ← hr]
    exact hx.2

/-- Some world meets the parts: no request yet, no account, no session, nothing accepted. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun _ _ => none, fun _ _ _ => False, [], [], fun _ _ => none, ServerState.mk [] [], ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp_all [frflow_defs]

end Keycloak.onlyTheSignedIn.Proofs
