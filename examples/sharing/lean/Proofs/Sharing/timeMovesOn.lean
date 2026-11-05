import FrFlowGen.Sharing.timeMovesOn.Spec
import Proofs.Sharing.Lemmas

/-! Time never goes back: a moment passed stays passed. The world's own step (`elapse`) moves the time by none or
more, where the schedule allows; a run of delivery, of housekeeping or of a request moves it only forwards (each tick
after a look at the clock, and each wait's end, `Lemmas.bounded_tick`, `Lemmas.bounded_move`, `Lemmas.run_clock`).
Delivery's steps at once commute as deliveryJob's do. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.timeMovesOn.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  unfold Sharing.timeMovesOn.claim
  intro t w _ _ _ ht
  refine ⟨⟨⟨fun x => ?_, ?_⟩, ?_⟩, fun r => ?_⟩
  · simp only [ClockModel.elapse_run, ClockModel.Ops.elapse_onWorld, FrFlow.runOn_guard, FrFlow.runOn_within,
      ClockModel.elapse, FrFlow.runOn_bind, FrFlow.runOn_get, FrFlow.runOn_set]
    have hle := FrFlow.Clock.move_le (fun w : World => w.clockModel) (fun (w : World) s => { w with clockModel := s })
      (fun w s => housekeepingOnTime s w.housekeptModel)
      (if (0 : Int) ≤ x then w.clockModel + x else w.clockModel) w (fun _ _ => rfl) (by split <;> omega)
    apply propext
    constructor
    · intro _; exact ht
    · intro _; exact Int.le_trans ht hle
  · have hc := Lemmas.run_clock w
    revert hc
    cases delivery_run w with
    | mk res after =>
      intro hc
      obtain ⟨_, h2⟩ := hc
      simp only at h2
      have e : (t ≤ after.clockModel) = (t ≤ w.clockModel) := propext ⟨fun _ => ht, fun _ => Int.le_trans ht h2⟩
      cases res with
      | error _ => exact ⟨trivial, e⟩
      | ok _ => exact ⟨e, trivial⟩
  · rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
    all_goals simp only [housekeeping_run, housekeeping, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
      FrFlow.runOnE_failing, FrFlow.runOnE_ite, FrFlow.runOnE_lift, LibraryModel.Ops.load_onWorldE,
      LibraryModel.Ops.save_onWorldE, HousekeptModel.Ops.ranAt_onWorldE, FrFlow.runOn_within, LibraryModel.load,
      LibraryModel.save, HousekeptModel.ranAt, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_pure,
      FrFlow.runOn_bind, FrFlow.runOn_modify, World.ticked_faults, World.ticked_libraryModel,
      World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
    all_goals refine ⟨?_, ?_⟩
    all_goals first
      | trivial
      | (apply propext; exact ⟨fun _ => ht, fun _ => by (repeat (first | exact Int.le_refl _ | exact ht | (refine Int.le_trans ht ?_) | (refine Lemmas.bounded_tick _ _ ?_) | (refine Lemmas.bounded_move _ _ _ (by first | omega | simp) ?_) | dsimp only))⟩)
      | (split <;> first
          | trivial
          | (rename_i heq
             (try split at heq)
             all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
               and_false] at heq)
             all_goals (try obtain ⟨rfl, rfl⟩ := heq)
             all_goals (try obtain ⟨-, rfl⟩ := heq)
             all_goals (apply propext; exact ⟨fun _ => ht, fun _ => by (repeat (first | exact Int.le_refl _ | exact ht | (refine Int.le_trans ht ?_) | (refine Lemmas.bounded_tick _ _ ?_) | (refine Lemmas.bounded_move _ _ _ (by first | omega | simp) ?_) | dsimp only))⟩)))
  · rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
    all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
      FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
      LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
      FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
      World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
    all_goals refine ⟨?_, ?_⟩
    all_goals first
      | trivial
      | (apply propext; exact ⟨fun _ => ht, fun _ => by (repeat (first | exact Int.le_refl _ | exact ht | (refine Int.le_trans ht ?_) | (refine Lemmas.bounded_tick _ _ ?_) | (refine Lemmas.bounded_move _ _ _ (by first | omega | simp) ?_) | dsimp only))⟩)
      | (split <;> first
          | trivial
          | (rename_i heq
             (try split at heq)
             all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
               and_false] at heq)
             all_goals (try obtain ⟨rfl, rfl⟩ := heq)
             all_goals (try obtain ⟨-, rfl⟩ := heq)
             all_goals (apply propext; exact ⟨fun _ => ht, fun _ => by (repeat (first | exact Int.le_refl _ | exact ht | (refine Int.le_trans ht ?_) | (refine Lemmas.bounded_tick _ _ ?_) | (refine Lemmas.bounded_move _ _ _ (by first | omega | simp) ?_) | dsimp only))⟩)))

/-- Two notices of the outbox's first ones sent at once, each with its own faults, commute: one notice, or two
people's mailboxes (`Lemmas.sends_commute`). The sleeps at once commute as FrFlow's automation shows. -/
theorem commute_2 : Obl.commute_2 := by
  unfold Obl.commute_2
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ h
  exact Lemmas.sends_commute n₁ n₂ (Lemmas.firstOfEach_apart _ _ _ h) w f₁ r₁ f₂ r₂ t₁ t₂

/-- Two removals from the outbox at once, each a transaction with its own faults, commute
(`Lemmas.removals_commute`). -/
theorem commute_6 : Obl.commute_6 := by
  unfold Obl.commute_6
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ _
  exact Lemmas.removals_commute n₁ n₂ w f₁ r₁ f₂ r₂ t₁ t₂

end Sharing.timeMovesOn.Proofs
