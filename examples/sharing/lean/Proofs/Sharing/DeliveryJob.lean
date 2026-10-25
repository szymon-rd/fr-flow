import FrFlowGen.Sharing.DeliveryJob.Spec

/-! Authored proofs of the obligations of DeliveryJob. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.DeliveryJob.Proofs
open Sharing.DeliveryJob

/-- Two notices of `firstOfEach` are to two people: each is the first in the outbox to its person. -/
theorem persons_differ (outbox : List Notice) (a b : Notice) (ha : a ∈ Sharing.Notifications.firstOfEach outbox)
    (hb : b ∈ Sharing.Notifications.firstOfEach outbox) (hab : a ≠ b) : a.to ≠ b.to := by
  intro h
  simp only [Sharing.Notifications.firstOfEach, List.mem_filter, decide_eq_true_eq] at ha hb
  have ha2 := ha.2
  rw [h] at ha2
  exact hab (Option.some.inj (ha2.symm.trans hb.2))

/-- With no call failing, two people's notices sent and taken out of the outbox in either order leave the same: two
mailboxes changed, and two removals from the outbox, which commute. -/
theorem commute_0 : Obl.commute_0 := by
  unfold Obl.commute_0
  intro lib n1 n2 w h1 h2 hne hf
  have hto := persons_differ _ _ _ h1 h2 hne
  have hfil : ∀ (xs : List Notice), List.filter (fun m => decide ¬m = n2) (List.filter (fun m => decide ¬m = n1) xs) =
      List.filter (fun m => decide ¬m = n1) (List.filter (fun m => decide ¬m = n2) xs) := by
    intro xs
    simp only [List.filter_filter]
    congr 1
    funext m
    exact Bool.and_comm _ _
  simp only [frflow_defs, hf, ite_true, hto, Ne.symm hto, ite_false, hfil]
  congr 2
  funext k
  by_cases hk1 : k = n1.to <;> by_cases hk2 : k = n2.to <;> simp_all
  all_goals congr 1

/-- What a branch of delivery may do to a world, keeping what the contract says of the run so far: give the mail server
the notice `x` (or not), and take it out of the outbox once the mail server has it (or not). -/
theorem keep (w s s' : World) (x : Notice) (hx : x ∈ Notifications.firstOfEach w.libraryStore.outbox) (h : post () w s)
    (hlib : s'.libraryStore = s.libraryStore ∨
      (s'.libraryStore = { s.libraryStore with outbox := List.filter (fun m => decide ¬m = x) s.libraryStore.outbox } ∧
        x ∈ (s'.mailer x.to).getD []))
    (hmail : s'.mailer = s.mailer ∨ s'.mailer = fun k =>
      if k = x.to then some (if x ∈ (s.mailer x.to).getD [] then (s.mailer x.to).getD [] else (s.mailer x.to).getD [] ++ [x])
      else s.mailer k) :
    post () w s' := by
  simp only [post, Notifications.mailbox, Notifications.taken] at h ⊢
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  -- the mail server keeps what it had
  have grows : ∀ p n, n ∈ (s.mailer p).getD [] → n ∈ (s'.mailer p).getD [] := by
    intro p n hn
    rcases hmail with hm | hm
    · rw [hm]; exact hn
    · rw [hm]
      by_cases hp : p = x.to
      · subst hp
        simp only [ite_true, Option.getD_some]
        by_cases hm' : n ∈ (s.mailer x.to).getD []
        · by_cases hx' : x ∈ (s.mailer x.to).getD []
          · simp only [hx', ↓reduceIte]; exact hn
          · simp only [hx', ↓reduceIte]; exact List.mem_append_left _ hn
        · exact absurd hn hm'
      · simp only [hp, ite_false]; exact hn
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rcases hlib with hl | ⟨hl, _⟩
    · rw [hl]; exact ha
    · rw [hl]
      have hout : s.libraryStore.outbox = List.filter (fun n => decide (n ∈ s.libraryStore.outbox)) w.libraryStore.outbox := by
        conv => lhs; rw [ha]
      rw [ha]
      simp only [Library.mk.injEq, true_and]
      rw [hout, List.filter_filter]
      congr 1
      funext m
      simp only [List.mem_filter, decide_eq_true_eq, Bool.and_eq_true]
      by_cases h1 : m = x <;> by_cases h2 : m ∈ w.libraryStore.outbox <;> simp [h1, h2]
  · intro n hn
    rcases hb n hn with hb1 | ⟨hh, hm⟩
    · rcases hlib with hl | ⟨hl, hxm⟩
      · left; rw [hl]; exact hb1
      · by_cases hnx : n = x
        · subst hnx; right; exact ⟨hx, hxm⟩
        · left; rw [hl]; simp only [List.mem_filter, hnx, decide_not, decide_false, Bool.not_false, and_true]; exact hb1
    · right; exact ⟨hh, grows _ _ hm⟩
  · intro n hn
    rcases hmail with hm | hm
    · rw [hm]; exact hc n hn
    · rw [hm]
      by_cases hp : n.to = x.to
      · have hnx : n = x := Classical.byContradiction fun hne => persons_differ _ _ _ hn hx hne hp
        subst hnx
        simp only [ite_true, Option.getD_some]
        rcases hc n hn with h1 | h1
        · rw [h1]; right; rfl
        · rw [h1]; right; by_cases hw : n ∈ (w.mailer n.to).getD [] <;> simp [hw]
      · simp only [hp, ite_false]; exact hc n hn

/-- A notice tried at the mail server three times, its outcome kept: the run never fails; the library is as it was; the
mail server has the notice (the outcome a success) or nothing new (a failure). -/
theorem sendTried (x : Notice) (s s' : World) (o : Except Failure (Except Failure Unit))
    (heq : FrFlow.runOnE (ε := Failure) ((tryCatchThe Failure (do
            let a ← tryCatchThe Failure (do
                Mailer.send x)
              (fun _ => do
                Clock.sleep 1
                tryCatchThe Failure (do
                    Mailer.send x)
                  (fun _ => do
                    Clock.sleep 2
                    Mailer.send x))
            pure (Except.ok a))
          (fun e => do
            pure (Except.error e))) : ExceptT Failure (StateM World) (Except Failure Unit)) s = (o, s')) :
    s'.libraryStore = s.libraryStore ∧
      ((o = .ok (.ok ()) ∧ s'.mailer = fun k =>
          if k = x.to then some (if x ∈ (s.mailer x.to).getD [] then (s.mailer x.to).getD [] else (s.mailer x.to).getD [] ++ [x])
          else s.mailer k) ∨
       ((∃ e, o = .ok (.error e)) ∧ s'.mailer = s.mailer)) := by
  simp only [frflow_defs] at heq
  rcases h1 : s.faults with _ | ⟨_ | _, f1⟩ <;> simp only [h1] at heq <;>
    (try (rcases h2 : f1 with _ | ⟨_ | _, f2⟩ <;> simp only [h2] at heq)) <;>
    (try (rcases h3 : f2 with _ | ⟨_ | _, f3⟩ <;> simp only [h3] at heq))
  all_goals (simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq)
  all_goals simp
  all_goals (funext k; congr)

/-- Taking a notice out of the outbox in one transaction, its outcome kept: the run never fails; the mail server is as
it was; the library is as it was (the store failed) or has the notice no longer in its outbox. -/
theorem removalTried (x : Notice) (s s' : World) (o : Except Failure (Except Failure Unit))
    (heq : FrFlow.runOnE (ε := Failure) ((tryCatchThe Failure (do
              let a_1 ← do
                let l ← LibraryStore.load
                LibraryStore.save { l with outbox := (List.filter (fun m => decide (¬(m = x))) l.outbox) }
              pure (Except.ok a_1))
            (fun e_1 => do
              pure (Except.error e_1))) : ExceptT Failure (StateM World) (Except Failure Unit)) s = (o, s')) :
    (∃ v, o = .ok v) ∧ s'.mailer = s.mailer ∧
      (s'.libraryStore = s.libraryStore ∨
        s'.libraryStore = { s.libraryStore with outbox := List.filter (fun m => decide ¬m = x) s.libraryStore.outbox }) := by
  simp only [frflow_defs] at heq
  rcases h1 : s.faults with _ | ⟨_ | _, f1⟩ <;> simp only [h1] at heq <;>
    (try (rcases h2 : f1 with _ | ⟨_ | _, f2⟩ <;> simp only [h2] at heq))
  all_goals (simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq)
  all_goals simp
  done

/-- The run reads the outbox, which may fail (and then nothing has changed); then each person's oldest notice is
delivered in turn, as Lean reads the branches (their commuting is `commute_0`): each keeps what the contract says of the
run so far (`keep`), whatever fails within it (`sendTried`, `removalTried`). -/
theorem impl : Obl.impl := by
  unfold Obl.impl Sharing.DeliveryJob.claim Sharing.deliveryJob_run Sharing.deliveryJob
  intro w
  rw [FrFlow.runOnE_bind, LibraryStore.load_onWorldE, FrFlow.runOnE_failing]
  simp only [FrFlow.runOn_within, LibraryModel.load, FrFlow.runOn_get]
  rcases hf : w.faults with _ | ⟨_ | _, fs⟩ <;> simp only
  case cons.true => simp [FrFlow.outcome, failure]
  all_goals
    apply FrFlow.outcome_mapM_void (P := fun s => post () w s)
    · intro x hx s hs
      rw [FrFlow.runOnE_bind]
      split
      · next a s1 heq =>
        obtain ⟨hl1, hm1⟩ := sendTried x s s1 (.ok a) heq
        rcases hm1 with ⟨ha, hm1⟩ | ⟨⟨e, ha⟩, hm1⟩
        · cases ha
          simp only [ite_true]
          rw [FrFlow.runOnE_bind]
          split
          · next o2 s2 heq2 =>
            obtain ⟨_, hm2, hl2⟩ := removalTried x s1 s2 (.ok o2) heq2
            simp only [FrFlow.runOnE_pure, Except.toBool, true_and]
            apply keep w s s2 x hx hs
            · rcases hl2 with hl2 | hl2
              · left; rw [hl2, hl1]
              · right; refine ⟨by rw [hl2, hl1], ?_⟩
                rw [hm2, hm1]
                by_cases hin : x ∈ (s.mailer x.to).getD [] <;> simp [hin]
            · right; rw [hm2, hm1]
          · next e2 s2 heq2 =>
            obtain ⟨⟨v, hv⟩, _⟩ := removalTried x s1 s2 (.error e2) heq2
            cases hv
        · cases ha
          simp only [ite_false, FrFlow.runOnE_pure, Except.toBool, true_and]
          exact keep w s s1 x hx hs (Or.inl hl1) (Or.inl hm1)
      · next e s1 heq =>
        obtain ⟨_, hm1⟩ := sendTried x s s1 (.error e) heq
        rcases hm1 with ⟨ha, _⟩ | ⟨⟨_, ha⟩, _⟩ <;> cases ha
    · intro s hs; exact hs
    · simp only [post, Notifications.mailbox, Notifications.taken]
      refine ⟨⟨?_, fun n hn => Or.inl hn⟩, fun n _ => Or.inl trivial⟩
      rw [List.filter_eq_self.2 (fun n hn => by simpa using hn)]

end Sharing.DeliveryJob.Proofs
