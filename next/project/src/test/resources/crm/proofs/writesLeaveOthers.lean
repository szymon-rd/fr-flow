import FrFlowGen.Crm.writesLeaveOthers.Spec
import Proofs.Crm.Lemmas

/-! A write of one company leaves what anyone finds of another's records as the history before it entitled them
to (today's expectation): it neither adds a record of the other company nor takes one back, and changes none of its
shares, since a share names a record by its id and no two records added have one id (`askedIn_unique`); what a
search finds is what the CRM holds (`visibility`, `storeMirrorsRequests`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writesLeaveOthers.Proofs
open Crm Crm.Lemmas

/-- A write by a user of another company neither adds a record of this one nor takes one back. -/
theorem records_other_write (es : List Event) (w : WriteCmd) (r : CrmRecord) (hOther : ¬r.tenant = w.«by».tenant) :
    r ∈ (askedIn (es ++ [Event.Wrote w])).records ↔ r ∈ (askedIn es).records := by
  rw [askedIn_snoc]
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add x =>
    simp only [askedStep]
    split
    · rename_i hAllowed
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hIn | rfl)
        · exact hIn
        · exact absurd hAllowed.1 hOther
      · exact Or.inl
    · exact Iff.rfl
  | ShareWith i to v =>
    simp only [askedStep]
    split <;> exact Iff.rfl
  | Unshare i to =>
    simp only [askedStep]
    split <;> exact Iff.rfl

/-- A write by a user of another company changes no share of a record of this one. -/
theorem shares_other_write (es : List Event) (w : WriteCmd) (r : CrmRecord) (c : TenantId) (T : Int)
    (hOther : ¬r.tenant = w.«by».tenant) (hAdded : r ∈ (askedIn es).records) :
    sharedIn (es ++ [Event.Wrote w]) r.id_ c T ↔ sharedIn es r.id_ c T := by
  have hIds := (askedIn_unique es).1
  simp only [sharedIn]
  rw [askedIn_snoc]
  generalize askedIn es = A at hIds hAdded
  rcases w with ⟨a, ch⟩
  have hOtherId : ∀ i, (∃ x ∈ A.records, x.id_ = i ∧ x.tenant = a.tenant) → ¬(r.id_ = i ∧ c = c) := by
    rintro i ⟨x, hx, hxi, hxa⟩ ⟨hri, _⟩
    have hSame := hIds x hx r hAdded (hxi.trans hri.symm)
    exact hOther (hSame ▸ hxa)
  cases ch with
  | Add x =>
    simp only [askedStep]
    split <;> exact Iff.rfl
  | ShareWith i to v =>
    simp only [askedStep]
    split
    · rename_i hAllowed
      have hNotPair : ¬(r.id_ = i ∧ c = to) := fun ⟨hri, _⟩ => hOtherId i hAllowed ⟨hri, rfl⟩
      rw [grant_append_other _ i to v T r.id_ c hNotPair, grant_filter_other A.grants i to T r.id_ c hNotPair]
    · exact Iff.rfl
  | Unshare i to =>
    simp only [askedStep]
    split
    · rename_i hAllowed
      have hNotPair : ¬(r.id_ = i ∧ c = to) := fun ⟨hri, _⟩ => hOtherId i hAllowed ⟨hri, rfl⟩
      rw [grant_filter_other A.grants i to T r.id_ c hNotPair]
    · exact Iff.rfl

theorem impl : Obl.impl := by
  intro history clock fetch held hk ho hM hV es w u q r hWrite
  obtain ⟨hHistory, hOther⟩ := hWrite
  obtain ⟨hRec, hShared⟩ := hM hk ho
  rw [hV hk ho u q r]
  simp only [mayRead]
  rw [hRec r, hShared r.id_ u.tenant, hHistory]
  apply propext
  by_cases hAdded : r ∈ (askedIn es).records
  · rw [records_other_write es w r hOther, shares_other_write es w r u.tenant clock hOther hAdded]
    constructor
    · rintro ⟨⟨hHeld, hAsks⟩, hMay⟩
      exact ⟨⟨hAsks, hHeld⟩, hMay⟩
    · rintro ⟨⟨hAsks, hHeld⟩, hMay⟩
      exact ⟨⟨hHeld, hAsks⟩, hMay⟩
  · rw [records_other_write es w r hOther]
    constructor
    · rintro ⟨⟨hHeld, _⟩, _⟩
      exact absurd hHeld hAdded
    · rintro ⟨⟨_, hHeld⟩, _⟩
      exact absurd hHeld hAdded

end Crm.writesLeaveOthers.Proofs
