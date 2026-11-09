import FrFlowGen.Sharing.accessRequestsAreAsks.Spec
import Proofs.Sharing.Lemmas

/-! The branch is its parts, line by line: asking keeps what is shared (askingChangesNothingKept), who answers
(onlyEditorsAnswer), and only while pending (approvedOnlyWhilePending); and, at every moment, each request held is
pending (requestsAnsweredOnTime), and reminded or not yet due (remindersOnTime), as of one housekeeping period ago,
read through what pending and due are. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.accessRequestsAreAsks.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers ownedBy isPending mayEdit chase hAsk _ _ _ _ _ hLapse hRemind world
    g0 g1 g2 g3 g4 g5 g6
  -- The lines about approving, of its code (the parts state them for every lifetime).
  have hApprove : ∀ lib t by_ p w, changes lib (approveCode (isPendingCode 604800) (mayEditCode inForce reaches covers)
      ownedBy lib t by_ p w) → mayEditCode inForce reaches covers lib t by_ w ∧
        pendingRequest (isPendingCode 604800) lib t p w := by
    intro lib t by_ p w h
    simp only [changes, approveCode] at h
    split at h
    · exact absurd rfl h
    · next r heq =>
      exact ⟨(Lemmas.changed h).1, r, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
  refine ⟨⟨⟨hAsk, fun lib t by_ p w => ⟨fun h => ?_, fun h => (hApprove lib t by_ p w h).2⟩⟩, fun r hr => ?_⟩,
    fun r hr => ?_⟩
  · rcases h with h | h
    · exact (hApprove lib t by_ p w h).1
    · exact Lemmas.changed h
  · have := hLapse world g0 g1 g2 g3 g4 g5 g6 r hr
    simp only [isPendingCode]
    omega
  · rcases hRemind world g0 g1 g2 g3 g4 g5 g6 r hr with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [reminderDueCode]; omega)

end Sharing.accessRequestsAreAsks.Proofs
