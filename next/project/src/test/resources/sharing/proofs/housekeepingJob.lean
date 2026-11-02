import FrFlowGen.Sharing.housekeepingJob.Spec

/-! A run of housekeeping on the models, one fault at a time: it reads the time and the library, and saves the library
housekeeping leaves when that changed it; a failed read changes nothing, and so does a failed save. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.housekeepingJob.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  intro w
  rcases w with ⟨lib, clock, boxes, pool, faults, races⟩
  rcases faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [housekeeping_run, housekeeping, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, ClockModel.Ops.now_onWorldE, LibraryModel.Ops.load_onWorldE,
    LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, ClockModel.now,
    LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind]
  all_goals refine ⟨?_, ?_⟩
  all_goals (try simp only [and_self])
  all_goals (try trivial)
  all_goals split
  all_goals (try trivial)
  all_goals rename_i heq
  all_goals (try split at heq)
  all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and] at heq)
  all_goals (try obtain ⟨rfl, rfl⟩ := heq)
  all_goals (try obtain ⟨-, rfl⟩ := heq)
  all_goals simp_all [housekeptAt]

end Sharing.housekeepingJob.Proofs
