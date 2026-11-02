import FrFlowGen.Sharing.deliveryJob.Spec
import Proofs.Sharing.Lemmas

/-! A run of delivery, notice by notice (`Lemmas.mapM_along`): each send leaves the mail server's mailbox of its
person as it was or with the notice taken, and the notice leaves the outbox only once the mail server has it, in one
transaction; the oldest notices of an outbox are of different people, so no send touches another's mailbox. A run that
loses its race with the time limit, or whose outbox cannot be read, changes neither. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.deliveryJob.Proofs
open Sharing


/-- A notice's delivery keeps what a run of delivery keeps once it has sent `done` (from the library `lib` and
the mailboxes `boxes` it began with: the library is it, some of its outbox kept; each notice of the outbox is still
there, or was sent and the mail server has it; no one's mailbox not sent to has changed, and each one's sent to is as
it was or holds their notice): it leaves the library as it was or its outbox without the notice, the mail server
having it, and the mailboxes as they were or the notice's person's with it taken. -/
theorem kept (lib : Library) (boxes : List Mailbox) (done rest : List Notice) (x : Notice) (s s' : World)
    (hsplit : done ++ x :: rest = firstOfEach lib.outbox) (hD : ((∃ keep : Notice → Bool, s.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
      (∀ n ∈ lib.outbox, n ∈ s.libraryModel.outbox ∨ (n ∈ done ∧ n ∈ mailbox s.mailerModel n.to)) ∧
      (∀ p, (∀ n ∈ done, n.to ≠ p) → mailbox s.mailerModel p = mailbox boxes p) ∧
      (∀ n ∈ done, mailbox s.mailerModel n.to = mailbox boxes n.to ∨
        mailbox s.mailerModel n.to = taken (mailbox boxes n.to) n)))
    (eff : (s'.libraryModel = s.libraryModel ∧ (s'.mailerModel = s.mailerModel ∨ s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x))) ∨
      (s'.libraryModel = { s.libraryModel with outbox := s.libraryModel.outbox.filter (fun m => decide ¬ m = x) } ∧
        s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x))) :
    ((∃ keep : Notice → Bool, s'.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
      (∀ n ∈ lib.outbox, n ∈ s'.libraryModel.outbox ∨ (n ∈ (done ++ [x]) ∧ n ∈ mailbox s'.mailerModel n.to)) ∧
      (∀ p, (∀ n ∈ (done ++ [x]), n.to ≠ p) → mailbox s'.mailerModel p = mailbox boxes p) ∧
      (∀ n ∈ (done ++ [x]), mailbox s'.mailerModel n.to = mailbox boxes n.to ∨
        mailbox s'.mailerModel n.to = taken (mailbox boxes n.to) n)) := by
  obtain ⟨⟨keep, hk⟩, h2, h3, h4⟩ := hD
  have hx : x ∈ firstOfEach lib.outbox := hsplit ▸ List.mem_append_right _ List.mem_cons_self
  have same : ∀ n ∈ done, n.to = x.to → n = x := fun n hn h =>
    Lemmas.firstOfEach_one _ _ _ (hsplit ▸ List.mem_append_left _ hn) hx h
  have hxbox : mailbox s.mailerModel x.to = mailbox boxes x.to ∨
      mailbox s.mailerModel x.to = taken (mailbox boxes x.to) x := by
    by_cases hin : ∃ n ∈ done, n.to = x.to
    · obtain ⟨n, hn, he⟩ := hin
      have := same n hn he
      subst this
      exact h4 n hn
    · exact Or.inl (h3 x.to (fun n hn he => hin ⟨n, hn, he⟩))
  have hW : ∀ p, mailbox (withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x)) p = if p = x.to then taken (mailbox s.mailerModel x.to) x
      else mailbox s.mailerModel p := fun p => Lemmas.mailbox_with _ _ _ _
  -- what a mailbox becomes: each person's as it was, but the notice's person's, its notice taken
  have boxOf : ∀ p, mailbox s'.mailerModel p = mailbox s.mailerModel p ∨
      (p = x.to ∧ mailbox s'.mailerModel p = taken (mailbox s.mailerModel x.to) x) := by
    intro p
    have hm : s'.mailerModel = s.mailerModel ∨ s'.mailerModel = withMailbox s.mailerModel x.to (taken (mailbox s.mailerModel x.to) x) := by
      rcases eff with ⟨_, hm⟩ | ⟨_, hm⟩
      · exact hm
      · exact Or.inr hm
    rcases hm with hm | hm
    · exact Or.inl (by rw [hm])
    · rw [hm, hW]
      by_cases hp : p = x.to
      · exact Or.inr ⟨hp, by simp [hp]⟩
      · exact Or.inl (by simp [hp])
  refine ⟨?_, fun n hn => ?_, fun p hp => ?_, fun n hn => ?_⟩
  · rcases eff with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact ⟨keep, hl.trans hk⟩
    · refine ⟨fun m => keep m && decide ¬ m = x, ?_⟩
      rw [hl, hk]
      simp [List.filter_filter, Bool.and_comm]
  · rcases h2 n hn with hin | ⟨hd, hm⟩
    · rcases eff with ⟨hl, hm⟩ | ⟨hl, hm⟩
      · exact Or.inl (hl ▸ hin)
      · by_cases hnx : n = x
        · subst hnx
          refine Or.inr ⟨List.mem_append_right _ (List.mem_singleton.2 rfl), ?_⟩
          rw [hm, hW]
          simp [Lemmas.mem_taken]
        · exact Or.inl (by rw [hl]; simp [hin, hnx])
    · refine Or.inr ⟨List.mem_append_left _ hd, ?_⟩
      rcases boxOf n.to with hb | ⟨he, hb⟩
      · exact hb ▸ hm
      · have := same n hd he
        subst this
        rw [hb]
        exact Lemmas.mem_taken _ _
  · have hpx : x.to ≠ p := hp x (List.mem_append_right _ (List.mem_singleton.2 rfl))
    rcases boxOf p with hb | ⟨he, _⟩
    · exact hb.trans (h3 p (fun n hn => hp n (List.mem_append_left _ hn)))
    · exact absurd he.symm hpx
  · by_cases he : n.to = x.to
    · have hnx : n = x := by
        rcases List.mem_append.1 hn with hn | hn
        · exact same n hn he
        · simpa using hn
      subst hnx
      rcases boxOf n.to with hb | ⟨_, hb⟩
      · exact hb ▸ hxbox
      · rw [hb]
        rcases hxbox with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inr (by rw [h, Lemmas.taken_taken])
    · have hd : n ∈ done := by
        rcases List.mem_append.1 hn with hn | hn
        · exact hn
        · exact absurd (by simp at hn; rw [hn]) he
      rcases boxOf n.to with hb | ⟨he', _⟩
      · exact hb ▸ h4 n hd
      · exact absurd he' he

set_option maxHeartbeats 2000000 in
theorem impl : Obl.impl := by
  unfold Obl.impl
  intro w
  rcases w with ⟨lib, clock, boxes, pool, faults, races⟩
  rcases races with _ | ⟨_ | _, rs⟩ <;> rcases faults with _ | ⟨_ | _, fs⟩
  all_goals simp only [delivery_run, delivery, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_throw, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, FrFlow.Races.leftWins_exceptT,
    FrFlow.Races.leftWins_onWorld, FrFlow.runOn_nextRace, PoolModel.Ops.take_onWorldE, PoolModel.Ops.give_onWorldE,
    LibraryModel.Ops.load_onWorldE, ClockModel.Ops.sleep_onWorldE, FrFlow.runOn_within, PoolModel.take,
    PoolModel.give, LibraryModel.load, ClockModel.sleep, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_modify,
    FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_map]
  all_goals first
    | (simp (config := { contextual := true }) [Lemmas.filter_mem_self, Lemmas.library_eta]; done)
    | (generalize hres : FrFlow.runOnE (List.mapM _ _) _ = res
       obtain ⟨bs, hbs, hinv⟩ : ∃ bs, res.1 = .ok bs ∧
           ((∃ keep : Notice → Bool, (res.2 : World).libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
           (∀ n ∈ lib.outbox, n ∈ (res.2 : World).libraryModel.outbox ∨ (n ∈ firstOfEach lib.outbox ∧ n ∈ mailbox (res.2 : World).mailerModel n.to)) ∧
           (∀ p, (∀ n ∈ firstOfEach lib.outbox, n.to ≠ p) → mailbox (res.2 : World).mailerModel p = mailbox boxes p) ∧
           (∀ n ∈ firstOfEach lib.outbox, mailbox (res.2 : World).mailerModel n.to = mailbox boxes n.to ∨
             mailbox (res.2 : World).mailerModel n.to = taken (mailbox boxes n.to) n)) := by
         rw [← hres]
         refine Lemmas.mapM_along _ (fun (done : List Notice) (s : World) =>
           ((∃ keep : Notice → Bool, s.libraryModel = { lib with outbox := lib.outbox.filter keep }) ∧
           (∀ n ∈ lib.outbox, n ∈ s.libraryModel.outbox ∨ (n ∈ done ∧ n ∈ mailbox s.mailerModel n.to)) ∧
           (∀ p, (∀ n ∈ done, n.to ≠ p) → mailbox s.mailerModel p = mailbox boxes p) ∧
           (∀ n ∈ done, mailbox s.mailerModel n.to = mailbox boxes n.to ∨
             mailbox s.mailerModel n.to = taken (mailbox boxes n.to) n))) _ ?_ _ ⟨⟨fun _ => true, by rw [List.filter_eq_self.2 (fun _ _ => rfl)]⟩, fun n hn => Or.inl hn,
           fun _ _ => rfl, fun _ hn => absurd hn List.not_mem_nil⟩
         intro done x rest s hsplit hD
         refine ⟨?_, kept lib boxes done rest x s _ hsplit hD ?_⟩
         · rcases s with ⟨l, c, b, p, fs, rs⟩
           iterate 5 (all_goals (try (rcases fs with _ | ⟨_ | _, fs⟩)); all_goals (try simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
  FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, MailerModel.Ops.send_onWorldE,
  ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE, LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within,
  MailerModel.send, ClockModel.sleep, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set,
  FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure]))
           all_goals simp
         · rcases s with ⟨l, c, b, p, fs, rs⟩
           iterate 5 (all_goals (try (rcases fs with _ | ⟨_ | _, fs⟩)); all_goals (try simp only [FrFlow.runOnE_bind, FrFlow.runOnE_pure,
  FrFlow.runOnE_lift, FrFlow.runOnE_failing, FrFlow.runOnE_tryCatch, FrFlow.runOnE_ite, MailerModel.Ops.send_onWorldE,
  ClockModel.Ops.sleep_onWorldE, LibraryModel.Ops.load_onWorldE, LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within,
  MailerModel.send, ClockModel.sleep, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set,
  FrFlow.runOn_modify, FrFlow.runOn_bind, FrFlow.runOn_pure]))
           all_goals simp
       rcases res with ⟨o, s'⟩
       simp only at hbs hinv
       subst hbs
       obtain ⟨⟨keep, hk⟩, h2, _, h4⟩ := hinv
       simp only
       refine ⟨⟨⟨?_, h2⟩, h4⟩, trivial⟩
       rw [hk]
       rw [Lemmas.filter_mem_filter])

end Sharing.deliveryJob.Proofs
