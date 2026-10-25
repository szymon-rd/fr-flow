import FrFlowGen.Sharing.HousekeepingClearsOnlyTheEnded.Spec

/-! Authored proofs of the obligations of HousekeepingClearsOnlyTheEnded. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.HousekeepingClearsOnlyTheEnded.Proofs
open Sharing.HousekeepingClearsOnlyTheEnded

/-- What tidying keeps is TidyContract's: a share it removes is not in force or of a document gone, an invitation not
open, a document gone. That ending is for good is EndedStaysEnded's second half. (Automation proved this before stage 4;
with the run's longer definitions in EndedStaysEnded's statement it gives up, so it is written out.) -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro tidy inForce gone isOpen events startedAt announce record isPending reminderDue hT hE
  unfold Sharing.HousekeepingClearsOnlyTheEnded.claim
  refine ⟨fun lib t => ?_, hE.2⟩
  have ht := hT lib t
  simp only [Sharing.TidyContract.post] at ht
  rw [ht]
  refine ⟨⟨fun s hs => ?_, fun i hi => ?_⟩, fun doc hd => ?_⟩
  · by_cases h1 : inForce s t
    · by_cases h2 : Sharing.Housekeeping.ofGone gone lib t s
      · right
        simp only [Sharing.Housekeeping.ofGone] at h2
        exact h2
      · left; left
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hs, h1, h2⟩
    · left; right; exact h1
  · by_cases h1 : isOpen i t
    · left; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hi, h1⟩
    · right; exact h1
  · by_cases h1 : gone doc t
    · right; exact h1
    · left; simp only [List.mem_filter, decide_eq_true_eq, decide_not]; simp [hd, h1]

end Sharing.HousekeepingClearsOnlyTheEnded.Proofs
