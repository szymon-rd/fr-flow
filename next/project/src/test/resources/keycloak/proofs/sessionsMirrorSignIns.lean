import FrFlowGen.Keycloak.sessionsMirrorSignIns.Spec
import Proofs.Keycloak.Lemmas

/-! The server's sessions mirror the sign-ins that still stand: its state is its requests handled in turn
(`serverRun`), and by induction over the history (`FrFlow.tracks`) each request handled as handleRequest says moves
the sessions as one more request moves the sign-ins (`liveIn_snoc`). Fresh tokens are what make a granted sign-in
open: no open session holds a token no earlier sign-in carried. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.sessionsMirrorSignIns.Proofs

theorem complete : Obl.complete := by
  intro history state seed step hRun hFresh hStep
  unfold serverRun.claim at hRun
  unfold freshTokens.claim at hFresh
  unfold handleRequest.claim at hStep
  have key := FrFlow.tracks (step := fun s q => step s q) (init := ServerState.mk seed [])
    (R := fun s es => (∀ (pre : List AuthRequest) (q : AuthRequest) (post : List AuthRequest),
        es = pre ++ q :: post → fresh pre q) →
      s.accounts = accountsAfter seed es ∧ ∀ x, x ∈ s.sessions ↔ liveIn seed es x)
    (by
      intro _
      refine ⟨by simp [accountsAfter], fun x => ?_⟩
      simp [Lemmas.liveIn_nil])
    (by
      intro s es e ih hf
      obtain ⟨hf0, hfe⟩ := Lemmas.fresh_snoc hf
      simp only [fresh] at hfe
      obtain ⟨hacc, hmem⟩ := ih hf0
      obtain ⟨⟨⟨tacc, tout⟩, tkeep⟩, topen⟩ := hStep s e
      refine ⟨by rw [tacc, hacc, Lemmas.accountsAfter_snoc], fun x => ?_⟩
      rw [Lemmas.liveIn_snoc]
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
          · cases ho
          · rename_i y hy
            split at ho
            · cases ho
            · cases ho; exact hy
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
            obtain ⟨p, hp, hpt⟩ := Lemmas.liveIn_token ((hmem y).1 hy)
            exact hfe x.token (Lemmas.grantedBy_token hg) ⟨p, hp, by rw [hpt, hyt]⟩
          simp only [opened, hg, hnone, ite_false])
  obtain ⟨_, hmem⟩ := key history (fun pre q post h => hFresh pre q post h)
  intro r x
  rw [hRun]
  apply propext
  simp only [Keycloak.sessions, Keycloak.stateAfter, List.mem_filter, decide_eq_true_eq]
  rw [hmem x]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- The parts hold together of the code: no request, the server's step over a store keeping what it is given. -/
theorem feasible : Obl.feasible := by
  refine ⟨[], _, [], Keycloak.handle (fun _ after => after), rfl, ?_, ?_⟩
  · frflow_auto
  · frflow_auto

end Keycloak.sessionsMirrorSignIns.Proofs
