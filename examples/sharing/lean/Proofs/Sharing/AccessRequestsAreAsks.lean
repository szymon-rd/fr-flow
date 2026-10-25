import FrFlowGen.Sharing.AccessRequestsAreAsks.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of AccessRequestsAreAsks. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.AccessRequestsAreAsks.Proofs
open Sharing.AccessRequestsAreAsks

/-- Asking changes only the requests (AskContract); approving needs an editor and a pending request (ApproveContract),
declining an editor (DeclineContract); and the deadline, with the timed words' contracts, says every request held is
pending, and reminded unless not yet due, one housekeeping period ago. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro ask approve inForce isPending decline events reminderDue startedAt announce record isOpen gone chase hAsk hApp hDec _ hP hD hT
  unfold Sharing.AccessRequestsAreAsks.claim
  refine ⟨⟨fun lib t p d level => ?_, fun lib t by_ p d => ⟨fun h => ?_, fun h => ?_⟩⟩, fun r hr => ?_⟩
  · rw [hAsk lib t p d level]; split <;> simp
  · rw [hApp lib t by_ p d] at h
    split at h
    · next r hf =>
      have hm := List.mem_of_find?_eq_some hf
      have hc := List.find?_some hf
      simp only [decide_eq_true_eq] at hc
      exact ⟨(Sharing.Lemmas.changed h).1, r, hm, hc⟩
    · exact absurd rfl h
  · rw [hDec lib t by_ p d] at h; exact Sharing.Lemmas.changed h
  · have ⟨h1, h2⟩ := hT r hr
    have e1 := hP r (((Sharing.Run.after startedAt announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy
      isOpen gone isPending reminderDue inForce) events).now - Sharing.housekeepingWithin)
    have e2 := hD r (((Sharing.Run.after startedAt announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy
      isOpen gone isPending reminderDue inForce) events).now - Sharing.housekeepingWithin)
    simp only [Sharing.PendingContract.post, Sharing.ReminderDueContract.post] at e1 e2
    rw [e1, e2]
    refine ⟨by omega, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · right; omega

end Sharing.AccessRequestsAreAsks.Proofs
