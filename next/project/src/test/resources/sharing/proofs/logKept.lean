import FrFlowGen.Sharing.logKept.Spec
import Proofs.Sharing.Lemmas

/-! The log's account kept at every step of the run (`logKept`): every share held has the entry that made it, every
notice of a change the entry it tells of. A request handled leaves
the library as it was or served at a moment (handleContract), a request served making only shares its entry tells of,
the entries before kept and its notices of its entry; a run of housekeeping leaves it housekept (housekeepingJob),
forgetting no entry that explains a share or a notice it keeps, its own notices of no logged change; delivery takes
notices out of the outbox and touches nothing else of the library (deliveryJob). A run that fails changes none of
it. Each run is of the code, what it calls as its code too. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.logKept.Proofs
open Sharing

theorem cover_deliver : Obl.cover_deliver := by
  unfold Obl.cover_deliver Sharing.logKept.keeps_deliver
  intro before g1 g2 g3
  have h := Lemmas.delivery_job before g1 g2 g3
  revert h
  cases delivery_run before with
  | mk res after =>
    cases res with
    | error e =>
      intro h
      obtain ⟨hlib, _⟩ := h.2
      refine ⟨trivial, ?_⟩
      show logKept after.libraryModel
      rw [hlib]; exact g3
    | ok u =>
      intro h
      obtain ⟨⟨hlib, _⟩, _⟩ := h.1
      refine ⟨?_, trivial⟩
      show logKept after.libraryModel
      rw [hlib]
      refine ⟨g3.1, fun n hn => g3.2 n ?_⟩
      exact (List.mem_filter.1 hn).1

theorem cover_housekeep : Obl.cover_housekeep := by
  unfold Obl.cover_housekeep Sharing.logKept.keeps_housekeep
  intro w _ _ g3
  have hk := Lemmas.housekept_logKept (isPendingCode 604800) (reminderDueCode 172800) (goneCode 2592000) inForceCode
    (isOpenCode 604800) w.libraryModel w.clockModel g3
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
    | exact g3
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
             | exact g3
             | (rename_i hc; rwa [if_pos hc] at hk)))

theorem cover_handle : Obl.cover_handle := by
  unfold Obl.cover_handle Sharing.logKept.keeps_handle
  intro r w _ _ g3
  rcases hf : w.faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, Lemmas.now_run,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind, World.ticked_faults, World.ticked_libraryModel,
    World.ticked_mailerModel, World.ticked_housekeptModel, World.ticked_poolModel, World.ticked_races, hf]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | exact g3
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
             | exact g3
             | exact Lemmas.served_logKept _ _ _ _ _ w.libraryModel _ r g3))

end Sharing.logKept.Proofs
