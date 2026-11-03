import FrFlowGen.Sharing.housekeptLately.Spec
import Proofs.Sharing.Lemmas

/-! Housekeeping ran no more than two minutes ago, and not later than now, at every step of the run. The world moves
the time on only where the schedule allows (`Lemmas.tick_lately`, `Lemmas.move_lately`): never more than two minutes
past housekeeping's last run, and never back. A request handled and a run of delivery leave when housekeeping ran as
it was; a run of housekeeping keeps the time it read, which is no later than the time after its tick, and that tick
was within two minutes of the run before, which is no later than it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.housekeptLately.Proofs
open Sharing

theorem cover_handle : Obl.cover_handle := by
  unfold Obl.cover_handle
  intros
  unfold Sharing.housekeptLately.keeps_handle
  intro r w g1 _ _
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | ((repeat (first | exact ‹housekeptLately _ _› | (simp only [World.ticked_housekeptModel, World.move_housekeptModel]) | (refine Lemmas.tick_lately _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) ?_) | (refine Lemmas.move_lately _ _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) (by first | simp | omega) ?_) | dsimp only)); done)
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals (repeat (first | exact ‹housekeptLately _ _› | (simp only [World.ticked_housekeptModel, World.move_housekeptModel]) | (refine Lemmas.tick_lately _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) ?_) | (refine Lemmas.move_lately _ _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) (by first | simp | omega) ?_) | dsimp only))))

theorem cover_housekeep : Obl.cover_housekeep := by
  unfold Obl.cover_housekeep
  intros
  unfold Sharing.housekeptLately.keeps_housekeep
  intro w g1 _ _
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [housekeeping_run, housekeeping, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, FrFlow.runOnE_lift, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, HousekeptModel.Ops.ranAt_onWorldE, FrFlow.runOn_within, LibraryModel.load,
    LibraryModel.save, HousekeptModel.ranAt, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_pure,
    FrFlow.runOn_bind, FrFlow.runOn_modify, World.ticked_faults, World.ticked_libraryModel, World.ticked_mailerModel,
    World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | ((repeat (first | exact ‹housekeptLately _ _› | (simp only [World.ticked_housekeptModel, World.move_housekeptModel]) | (refine Lemmas.tick_lately _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) ?_) | (refine Lemmas.move_lately _ _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) (by first | simp | omega) ?_) | dsimp only)); done)
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals (try (repeat (first | exact ‹housekeptLately _ _› | (simp only [World.ticked_housekeptModel, World.move_housekeptModel]) | (refine Lemmas.tick_lately _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) ?_) | (refine Lemmas.move_lately _ _ _ (by simp [World.ticked_housekeptModel, World.move_housekeptModel]) (by first | simp | omega) ?_) | dsimp only)))
           all_goals (have hl := Lemmas.tick_le w
                      have hw := Lemmas.tick_within w
                      simp only [housekeptLately] at g1 ⊢
                      omega)))

theorem cover_deliver : Obl.cover_deliver := by
  unfold Obl.cover_deliver Sharing.housekeptLately.keeps_deliver
  intro w g1 _ _
  have h := Lemmas.run_clock w (by simp only [housekeptLately] at g1; omega)
  revert h
  cases delivery_run w with
  | mk res after =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    have hl : housekeptLately after.clockModel after.housekeptModel := by
      simp only [housekeptLately] at g1 ⊢
      simp only at h1 h2 h3
      omega
    cases res with
    | error e => exact ⟨trivial, hl⟩
    | ok u => exact ⟨hl, trivial⟩

end Sharing.housekeptLately.Proofs
