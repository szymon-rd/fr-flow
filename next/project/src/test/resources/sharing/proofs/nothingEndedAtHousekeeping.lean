import FrFlowGen.Sharing.nothingEndedAtHousekeeping.Spec
import Proofs.Sharing.Lemmas

/-! Nothing in the library had ended when housekeeping last ran, at every step of the run. A request handled keeps
when housekeeping ran and serves the library at a time no earlier than now (`Lemmas.tick_le`), which is no earlier
than housekeeping's last run (housekeptLately): what it trashes, sends or asks it does then
(`Lemmas.served_nothingEnded`). A run of housekeeping
leaves nothing ended as of the time it read, which it keeps (`Lemmas.housekept_nothingEnded`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.nothingEndedAtHousekeeping.Proofs
open Sharing

theorem cover_handle : Obl.cover_handle := by
  unfold Obl.cover_handle Sharing.nothingEndedAtHousekeeping.keeps_handle
  intro r w g1 g2 _
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals have ht : w.housekeptModel ≤ (FrFlow.Clock.ticked (fun (w : World) => w.ticks) (fun (w : World) s => { w with ticks := s }) (fun (w : World) => w.clockModel) (fun (w : World) s => { w with clockModel := s }) (fun (w : World) s => housekeepingOnTime s w.housekeptModel) w).clockModel := Int.le_trans g1.1 (Lemmas.tick_le w)
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | exact g2
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals simp only [World.ticked_libraryModel, World.ticked_housekeptModel]
           all_goals first
             | exact g2
             | exact Lemmas.served_nothingEnded _ _ _ _ _ w.libraryModel _ r _ g2 ht))

/-- Housekeeping leaves nothing ended as of the time it read, which it keeps as its last run
(`Lemmas.housekept_nothingEnded`); a run that fails changes neither the library nor when it last ran. -/
theorem cover_housekeep : Obl.cover_housekeep := by
  unfold Obl.cover_housekeep Sharing.nothingEndedAtHousekeeping.keeps_housekeep
  intro w _ g2 _
  have hk := Lemmas.housekept_nothingEnded w.libraryModel w.clockModel
  simp only [housekeptAt] at hk
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
    | exact g2
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals simp only [World.ticked_libraryModel, World.ticked_housekeptModel]
           all_goals first
             | exact g2
             | (rename_i hc; first | rwa [if_pos hc] at hk | rwa [if_neg hc] at hk)))

/-- Delivery takes notices out of the outbox only (deliveryJob), or changes nothing, and keeps when housekeeping ran
(`Lemmas.run_clock`). -/
theorem cover_deliver : Obl.cover_deliver := by
  unfold Obl.cover_deliver Sharing.nothingEndedAtHousekeeping.keeps_deliver
  intro w g1 g2 g3
  have hc := Lemmas.run_clock w (by simp only [housekeptLately] at g1; omega)
  have h := Lemmas.delivery_job w g1 g2 g3
  revert h hc
  cases delivery_run w with
  | mk res after =>
    intro hc h
    obtain ⟨hk, _, _⟩ := hc
    simp only at hk
    cases res with
    | error e =>
      obtain ⟨hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show nothingEndedAtHousekeeping after.libraryModel after.housekeptModel
      rw [hlib, hk]; exact g2
    | ok u =>
      obtain ⟨⟨hlib, _⟩, _⟩ := h.1
      refine ⟨?_, trivial⟩
      show nothingEndedAtHousekeeping after.libraryModel after.housekeptModel
      rw [hlib, hk]; exact g2

end Sharing.nothingEndedAtHousekeeping.Proofs
