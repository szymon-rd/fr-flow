import FrFlowGen.Sharing.HandleContract.Spec

/-! Authored proofs of the obligations of HandleContract. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.HandleContract.Proofs
open Sharing.HandleContract

/-- The handling reads the clock and the library, saves what the request leads to when it differs, and answers: the
store then holds what the request leads to either way, and the clock is as it was. Nothing of the operations is used. -/
theorem impl : Obl.impl := by
  unfold Obl.impl
  intro share unshare move invite accept withdraw trash restore access inForce isOpen gone _ _ _ _ _ _ _ _ _ _ _
  unfold Sharing.HandleContract.claim Sharing.HandleContract.post Sharing.handleContract_run Sharing.handleContract
  intro r w
  simp only [FrFlow.runOn_bind, Clock.now_onWorld, LibraryStore.load_onWorld, FrFlow.runOn_within, ClockModel.now,
    LibraryModel.load, FrFlow.runOn_get, FrFlow.runOn_pure]
  by_cases h : SharingHttp.afterRequest share unshare move invite accept withdraw trash restore w.libraryStore w.clock.now r =
    w.libraryStore
  · simp [h, FrFlow.runOn_pure]
  · simp [h, FrFlow.runOn_map, LibraryStore.save_onWorld, FrFlow.runOn_within, LibraryModel.save, FrFlow.runOn_set]

end Sharing.HandleContract.Proofs
