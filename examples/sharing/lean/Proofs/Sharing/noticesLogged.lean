import FrFlowGen.Sharing.noticesLogged.Spec
import Proofs.Sharing.Lemmas

/-! Every waiting notice of a logged change has its entry, at every step of the run. A request handled leaves
the library as it was or served at a moment, its notices of its entry (`Lemmas.served_logKept`); a run of
housekeeping leaves it housekept, forgetting no entry a notice it keeps tells of, its own notices of no logged change
(`Lemmas.housekept_logKept`); delivery only takes notices out of the outbox (deliveryJob). A run that fails changes
none of it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.noticesLogged.Proofs
open Sharing

theorem cover_deliver : Obl.cover_deliver := by
  unfold Obl.cover_deliver Sharing.noticesLogged.keeps_deliver
  intro before g0 g1 g2 g3 g4 g5 g6
  have h := Lemmas.delivery_job before g0 g1 g2 g3 g4 g5 g6
  revert h
  cases delivery_run before with
  | mk res after =>
    cases res with
    | error e =>
      intro h
      obtain ⟨hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show noticesLogged after.libraryModel
      rw [hlib]; exact g6
    | ok u =>
      intro h
      obtain ⟨⟨hlib, _⟩, _⟩ := h.1
      refine ⟨?_, trivial⟩
      show noticesLogged after.libraryModel
      simp only [onlyTakenOut] at hlib
      rw [hlib]; exact fun n hn => g6 n (List.mem_filter.1 hn).1

theorem cover_housekeep : Obl.cover_housekeep := by
  unfold Obl.cover_housekeep Sharing.noticesLogged.keeps_housekeep
  intro w g0 g1 g2 g3 g4 g5 g6
  have hk := (Lemmas.housekept_logKept (isPendingCode 604800) (reminderDueCode 172800) (goneCode 2592000) inForceCode
    (isOpenCode 604800) w.libraryModel w.clockModel ⟨g5, g6⟩).2
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
    | exact g6
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
             | exact g6
             | (rename_i hc; rwa [if_pos hc] at hk)))

theorem cover_handle : Obl.cover_handle := by
  unfold Obl.cover_handle Sharing.noticesLogged.keeps_handle
  intro r w g0 g1 g2 g3 g4 g5 g6
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | exact g6
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
             | exact g6
             | exact (Lemmas.served_logKept _ _ _ _ _ w.libraryModel _ r ⟨g5, g6⟩).2))

end Sharing.noticesLogged.Proofs
