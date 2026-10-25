import FrFlowGen.Sharing.EndedStaysEnded.Spec

/-! Authored proofs of the obligations of EndedStaysEnded. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.EndedStaysEnded.Proofs
open Sharing.EndedStaysEnded

/-- Each event keeps the time or moves it on, a wait by what the clock allows (ClockNeverGoesBack); and each lifetime,
once over, is over at every later time (its contract). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events inForce isOpen gone startedAt hF hO hG hC
  unfold Sharing.EndedStaysEnded.claim
  refine ⟨fun pre post hev => ?_, fun t u htu => ⟨⟨fun s hs => ?_, fun i hi => ?_⟩, fun doc hd => ?_⟩⟩
  · subst hev
    unfold Sharing.Run.after
    exact FrFlow.along_when (Sharing.Run.step (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) isOpen gone inForce)
      (fun _ e => match e with | Event.Asked _ => True | Event.Housekept => True | Event.Waited d => d ≥ 0)
      (fun a b => a.now ≤ b.now) _ (fun _ => Int.le_refl _) (fun _ _ _ h1 h2 => Int.le_trans h1 h2)
      (fun m e ok => by cases e <;> simp [Sharing.Run.step] at ok ⊢ <;> omega)
      pre post (fun p e q h => hC p q e h)
  · have h1 := hF s t; have h2 := hF s u
    simp only [Sharing.InForceContract.post] at h1 h2
    rw [h1] at hs; rw [h2]
    cases h : s.«until» <;> simp [h] at hs ⊢ <;> omega
  · have h1 := hO i t; have h2 := hO i u
    simp only [Sharing.IsOpenContract.post] at h1 h2
    rw [h1] at hi; rw [h2]
    omega
  · have h1 := hG doc t; have h2 := hG doc u
    simp only [Sharing.GoneContract.post] at h1 h2
    rw [h1] at hd; rw [h2]
    cases h : doc.trashed <;> simp [h] at hd ⊢ <;> omega

end Sharing.EndedStaysEnded.Proofs
