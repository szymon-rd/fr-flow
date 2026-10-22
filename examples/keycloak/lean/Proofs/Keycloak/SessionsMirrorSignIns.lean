import FrFlowGen.Keycloak.SessionsMirrorSignIns.Spec
import Proofs.Keycloak.Lemmas

/-! Authored proof that the server's sessions mirror the sign-ins that still stand: by induction over
the history (`FrFlow.tracks`), each request handled as HandleRequest says moves the sessions as one more
request moves the sign-ins (`liveIn_snoc`). Fresh tokens are what make a granted sign-in open: no open
session holds a token no earlier sign-in carried. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.SessionsMirrorSignIns.Proofs
open Keycloak Keycloak.Lemmas

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history step seed hFresh hStep
  simp only [Keycloak.FreshTokens.claim, Keycloak.HandleRequest.claim] at hFresh hStep
  -- What every state reached holds, for a history whose sign-ins carry fresh tokens.
  have key := FrFlow.tracks (step := fun s q => step s q) (init := ServerState.mk seed [])
    (R := fun s es => (∀ (pre post : List AuthRequest) (q : AuthRequest), es = pre ++ q :: post → fresh pre q) →
      s.accounts = accountsAfter seed es ∧ ∀ x, x ∈ s.sessions ↔ liveIn seed es x)
    (by
      intro _
      refine ⟨by simp [accountsAfter], fun x => ?_⟩
      show x ∈ ([] : List Session) ↔ _
      simp [liveIn_nil])
    (by
      intro s es e ih hf
      obtain ⟨hf0, hfe⟩ := fresh_snoc hf
      simp only [fresh] at hfe
      obtain ⟨hacc, hmem⟩ := ih hf0
      obtain ⟨⟨⟨tacc, tout⟩, tkeep⟩, topen⟩ := hStep s e
      refine ⟨by rw [tacc, hacc, accountsAfter_snoc], fun x => ?_⟩
      rw [liveIn_snoc]
      constructor
      · intro hx
        rcases tout x hx with ⟨hxs, hne⟩ | ho
        · refine Or.inl ⟨(hmem x).1 hxs, ?_⟩
          rintro rfl
          exact hne (by simp [endedBy])
        · refine Or.inr ?_
          rw [← hacc]
          simp only [opened] at ho
          split at ho
          · rename_i y hy
            split at ho
            · cases ho
            · cases ho; exact hy
          · cases ho
      · rintro (⟨hl, hne⟩ | hg)
        · rcases tkeep x ((hmem x).2 hl) with he | ht
          · exfalso
            cases e with
            | SignOut r t =>
              simp only [endedBy] at he
              obtain ⟨h1, h2⟩ := he
              exact hne (by rw [h1, h2])
            | SignIn r u pw t => simp [endedBy] at he
            | SetEnabled r u on => simp [endedBy] at he
          · exact ht
        · apply topen x
          rw [← hacc] at hg
          have hnone : ¬ ∃ y ∈ s.sessions, y.token = x.token := by
            rintro ⟨y, hy, hyt⟩
            obtain ⟨p, hp, hpt⟩ := liveIn_token ((hmem y).1 hy)
            exact hfe x.token (grantedBy_token hg) ⟨p, hp, by rw [hpt, hyt]⟩
          simp only [opened, hg, hnone, ite_false])
  obtain ⟨_, hmem⟩ := key history hFresh
  intro r x
  apply propext
  simp only [Keycloak.sessions, Keycloak.stateAfter, List.mem_filter, decide_eq_true_eq]
  rw [hmem x]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

end Keycloak.SessionsMirrorSignIns.Proofs
