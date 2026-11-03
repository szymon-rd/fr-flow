import FrFlowGen.Sharing.housekeepingJob.Spec
import Proofs.Sharing.Lemmas

/-! A run of housekeeping on the models, one fault at a time: it reads the time (the world's tick after) and the
library, saves the library housekeeping leaves at that time when that changed it, and keeps that time as housekeeping's
last run; a failed read changes nothing of the stores, and so does a failed save. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.housekeepingJob.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  intro w _ _ _
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
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and,
             and_false] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals (try obtain ⟨-, rfl⟩ := heq)
           all_goals simp only [World.ticked_libraryModel, World.ticked_mailerModel, World.ticked_housekeptModel,
             World.ticked_poolModel, and_self, and_true, housekeptAt]
           all_goals (try simp_all)))

end Sharing.housekeepingJob.Proofs
