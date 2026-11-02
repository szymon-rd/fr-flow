import FrFlowGen.Sharing.handleContract.Spec

/-! The handling's run on the models, one fault at a time: reading the time and the library at once, it saves the
library the request leads to when it changed, and answers within the time limit (the clock moves only by sleeps,
so it is never past); a failed read changes nothing, and so does a failed save. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.handleContract.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers inTrash mayView _ _ _ _ _
  intro r w
  rcases w with ⟨lib, clock, boxes, pool, faults, races⟩
  rcases faults with _ | ⟨_ | _, _ | ⟨_ | _, fs⟩⟩
  all_goals simp only [handleRequest_run, handleRequest, FrFlow.runOnE_bind, FrFlow.runOnE_pure, FrFlow.runOnE_lift,
    FrFlow.runOnE_failing, FrFlow.runOnE_ite, ClockModel.Ops.now_onWorldE, LibraryModel.Ops.load_onWorldE, LibraryModel.Ops.save_onWorldE, FrFlow.runOn_within, ClockModel.now,
    LibraryModel.load, LibraryModel.save, FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_pure, FrFlow.runOn_bind]
  all_goals refine ⟨?_, ?_⟩
  all_goals (try simp only [and_self])
  all_goals first
    | trivial
    | (split <;> first
        | trivial
        | (rename_i heq
           (try split at heq)
           all_goals (try simp only [Prod.mk.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq, false_and] at heq)
           all_goals (try obtain ⟨rfl, rfl⟩ := heq)
           all_goals simp_all))

end Sharing.handleContract.Proofs
