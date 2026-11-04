import FrFlowGen.Sharing.accessRequestsAreAsks.Spec
import Proofs.Sharing.Lemmas

/-! Asking changes only the requests; approving changes the library only through a pending request of the person
when the asker may edit, declining only when the asker may edit. At every moment each request held is pending, and
reminded or not yet due, as of one housekeeping period ago: requestsAnsweredOnTime. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.accessRequestsAreAsks.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers ownedBy chase _ _ _ _ _ _ hOnTime world g1 g2 g3
  refine ⟨⟨fun lib t p w level => ?_, fun lib t by_ p w => ⟨fun h => ?_, fun h => Lemmas.changed h⟩⟩,
    fun r hr => ?_⟩
  · simp only [askCode]
    split <;> exact ⟨⟨rfl, rfl⟩, rfl⟩
  · simp only [approveCode] at h
    split at h
    · exact absurd rfl h
    · next r heq =>
      have hc := Lemmas.changed h
      exact ⟨hc.1, r, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
  · obtain ⟨h1, h2⟩ := hOnTime world g1 g2 g3 r hr
    simp only [isPendingCode, reminderDueCode]
    refine ⟨by omega, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by omega)

end Sharing.accessRequestsAreAsks.Proofs
