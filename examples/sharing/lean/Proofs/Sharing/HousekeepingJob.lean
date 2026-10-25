import FrFlowGen.Sharing.HousekeepingJob.Spec

/-! Authored proofs of the obligations of HousekeepingJob. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.HousekeepingJob.Proofs
open Sharing.HousekeepingJob

/-- The run reads the clock and the library, saves what tidying, forgetting, chasing and telling of ending shares leave
(recorded) when it differs, and stops. For each case of the store's faults: the load fails, or the save fails, and
nothing has changed; or both go through. The clock and the mail server are as they were. Nothing of the operations is
used: the flow calls them as the contract states them. -/
theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  unfold Sharing.HousekeepingJob.claim Sharing.HousekeepingJob.post Sharing.HousekeepingJob.failure
    Sharing.housekeepingJob_run Sharing.housekeepingJob
  intro w
  simp only [FrFlow.runOnE_bind, Clock.now_onWorldE, LibraryStore.load_onWorldE, LibraryStore.save_onWorldE, FrFlow.runOnE_lift,
    FrFlow.runOnE_failing, FrFlow.runOn_within, ClockModel.now, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOnE_pure, FrFlow.runOnE_ite, FrFlow.runOnE_seqRight]
  frflow_faults
  all_goals (try split)
  all_goals frflow_faults
  all_goals simp_all [FrFlow.outcome]

end Sharing.HousekeepingJob.Proofs
