import FrFlowGen.Crm.addedIsFound.Spec
import Proofs.Crm.Lemmas

/-! A record added is found from then on (today's expectation): right after the add it is added, and nothing asked
after it takes it back (`askedIn_records_append`); so the CRM holds it (`storeMirrorsRequests`), and a search asking
for it returns it, the record being of the user's company (`visibility`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.addedIsFound.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro history fetch held clock hk ho hM hV u r pre post q hAdd hAsks
  obtain ⟨⟨hHistory, hTenant⟩, hFresh⟩ := hAdd
  have hAdded : r ∈ (askedIn (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))])).records := by
    rw [askedIn_snoc]
    simp only [askedStep]
    rw [ite_eq_left ⟨hTenant, hFresh⟩]
    simp
  have hNow : r ∈ (askedIn history).records := by
    have hSplit : history = (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))]) ++ post := by simp [hHistory]
    rw [hSplit]
    exact askedIn_records_append _ post hAdded
  rw [hV hk ho u q r, (hM hk ho).1 r]
  exact ⟨⟨hNow, hAsks⟩, Or.inl hTenant⟩

end Crm.addedIsFound.Proofs
