import FrFlowGen.Sharing.HandleContract.Spec

/-! Authored proofs of the obligations of HandleContract. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.HandleContract.Proofs
open Sharing.HandleContract

/-- The handling reads the clock and the library, saves what the request leaves when it differs, and answers. For each
case of the store's faults: the load fails, and nothing has changed; the save fails, and nothing has changed (a failed
save changes nothing); or both go through, and the store holds what the request leaves. The clock and the mail server
are as they were either way. Nothing of the operations is used. -/
theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  unfold Sharing.HandleContract.claim Sharing.HandleContract.post Sharing.HandleContract.failure
    Sharing.handleContract_run Sharing.handleContract
  intro r w
  simp only [FrFlow.runOnE_bind, Clock.now_onWorldE, LibraryStore.load_onWorldE, LibraryStore.save_onWorldE, FrFlow.runOnE_lift,
    FrFlow.runOnE_failing, FrFlow.runOn_within, ClockModel.now, LibraryModel.load, LibraryModel.save, FrFlow.runOn_get,
    FrFlow.runOn_set, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOnE_pure, FrFlow.runOnE_ite, FrFlow.runOnE_seqRight]
  frflow_faults
  all_goals (try split)
  all_goals frflow_faults
  all_goals simp_all [FrFlow.outcome]

end Sharing.HandleContract.Proofs
