import FrFlowGen.Crm.SharedCrm.Spec
import Proofs.Crm.Lemmas

/-! The root from its parts, and its expectations. A search returns the stored records it asks for that
the user may read now (Visibility); the CRM holds exactly the records users added, and a share as
current exactly when its company shared it so (StoreMirrorsRequests). So a search finds what users
asked. The expectations are said of the history: a concrete one (Ann and Gil), an added record found
from then on (what is added stays added: `askedIn_records_append`), and a write of one company leaving
what anyone finds of another's records as it was (one record per id: `askedIn_unique`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.SharedCrm.Proofs
open Crm Crm.SharedCrm Crm.Lemmas

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  simp only [Crm.SharedCrm.claim, Crm.StoreMirrorsRequests.claim, Crm.Visibility.claim] at *
  obtain ⟨hRecords, hShared⟩ := h_StoreMirrorsRequests
  intro u q r
  simp only [Crm.finds, Crm.asksFor, Crm.added, Crm.owner, Crm.companyOf, Crm.sharedWith]
  rw [h_Visibility u q r]
  simp only [Crm.mayRead]
  rw [hRecords r, hShared r.id_ u.tenant]
  apply propext
  constructor
  · rintro ⟨⟨hHeld, hAsks⟩, hMay⟩
    exact ⟨⟨hAsks, trivial, hHeld⟩, hMay⟩
  · rintro ⟨⟨hAsks, _, hHeld⟩, hMay⟩
    exact ⟨⟨hHeld, hAsks⟩, hMay⟩

theorem expect_0 : Obl.expect_0 := by
  unfold Obl.expect_0
  frflow_intro
  simp only [Crm.SharedCrm.claim, Crm.SharedCrm.expected_0, Crm.finds, Crm.asksFor, Crm.added, Crm.owner,
    Crm.companyOf, Crm.sharedWith] at *
  intro hHistory
  -- What this history asked: Ann's contact and Globex's deal added, the deal shared with Acme until 100.
  have hAsked : askedIn history = Asked.mk
      [CrmRecord.mk 1 (TenantId.mk "acme") Kind.Contact "Acme contact", CrmRecord.mk 2 (TenantId.mk "globex") Kind.Deal "Globex deal"]
      [Grant.mk 2 (TenantId.mk "acme") (some 100)] := by
    rw [hHistory]
    simp [Crm.askedIn, Crm.askedStep]
  simp only [h, Crm.sharedIn, hAsked]
  refine ⟨⟨fun hClock => ?_, fun hClock => ?_⟩, ?_⟩
  · simp [hClock, Crm.askMatches, Crm.matches]
  · simp [hClock, Crm.askMatches, Crm.matches]
  · simp [Crm.askMatches, Crm.matches]

theorem expect_1 : Obl.expect_1 := by
  unfold Obl.expect_1
  frflow_intro
  simp only [Crm.SharedCrm.claim, Crm.SharedCrm.expected_1, Crm.finds, Crm.asksFor, Crm.added, Crm.owner,
    Crm.companyOf, Crm.sharedWith] at *
  intro u r pre post ⟨⟨hHistory, hTenant⟩, hFresh⟩ q hAsks
  -- Right after the add, it is added; nothing asked after it takes it back.
  have hAdded : r ∈ (askedIn (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))])).records := by
    rw [askedIn_snoc]
    simp only [Crm.askedStep]
    rw [ite_eq_left ⟨hTenant, hFresh⟩]
    simp
  have hNow : r ∈ (askedIn history).records := by
    have hSplit : history = (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))]) ++ post := by simp [hHistory]
    rw [hSplit]
    exact askedIn_records_append _ post hAdded
  rw [h u q r]
  exact ⟨⟨hAsks, trivial, hNow⟩, Or.inl hTenant⟩

/-- A write by a user of another company neither adds a record of this one nor takes one back. -/
theorem records_other_write (es : List Event) (w : WriteCmd) (r : CrmRecord) (hOther : r.tenant ≠ w.by.tenant) :
    r ∈ (askedIn (es ++ [Event.Wrote w])).records ↔ r ∈ (askedIn es).records := by
  rw [askedIn_snoc]
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add x =>
    simp only [Crm.askedStep]
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
    simp only [Crm.askedStep]
    split <;> exact Iff.rfl
  | Unshare i to =>
    simp only [Crm.askedStep]
    split <;> exact Iff.rfl

/-- A write by a user of another company changes no share of a record of this one: a share names a
record by its id, and no two records added have one id. -/
theorem shares_other_write (es : List Event) (w : WriteCmd) (r : CrmRecord) (c : TenantId) (T : Int)
    (hOther : r.tenant ≠ w.by.tenant) (hAdded : r ∈ (askedIn es).records) :
    sharedIn (es ++ [Event.Wrote w]) r.id_ c T ↔ sharedIn es r.id_ c T := by
  have hIds := (askedIn_unique es).1
  simp only [Crm.sharedIn]
  rw [askedIn_snoc]
  generalize askedIn es = A at hIds hAdded
  rcases w with ⟨a, ch⟩
  -- A share or unshare of another company's record names an id other than this record's.
  have hOtherId : ∀ i, (∃ x ∈ A.records, x.id_ = i ∧ x.tenant = a.tenant) → ¬(r.id_ = i ∧ c = c) := by
    rintro i ⟨x, hx, hxi, hxa⟩ ⟨hri, _⟩
    have hSame := hIds x hx r hAdded (hxi.trans hri.symm)
    exact hOther (hSame ▸ hxa)
  cases ch with
  | Add x =>
    simp only [Crm.askedStep]
    split <;> exact Iff.rfl
  | ShareWith i to v =>
    simp only [Crm.askedStep]
    split
    · rename_i hAllowed
      have hNotPair : ¬(r.id_ = i ∧ c = to) := fun ⟨hri, _⟩ => hOtherId i hAllowed ⟨hri, rfl⟩
      rw [grant_append_other _ i to v T r.id_ c hNotPair, grant_filter_other A.grants i to T r.id_ c hNotPair]
    · exact Iff.rfl
  | Unshare i to =>
    simp only [Crm.askedStep]
    split
    · rename_i hAllowed
      have hNotPair : ¬(r.id_ = i ∧ c = to) := fun ⟨hri, _⟩ => hOtherId i hAllowed ⟨hri, rfl⟩
      rw [grant_filter_other A.grants i to T r.id_ c hNotPair]
    · exact Iff.rfl

theorem expect_2 : Obl.expect_2 := by
  unfold Obl.expect_2
  frflow_intro
  simp only [Crm.SharedCrm.claim, Crm.SharedCrm.expected_2, Crm.finds, Crm.asksFor, Crm.added, Crm.owner,
    Crm.companyOf, Crm.sharedWith] at *
  intro es w u q r ⟨hHistory, hOther⟩
  rw [h u q r, hHistory]
  apply propext
  by_cases hAdded : r ∈ (askedIn es).records
  · rw [records_other_write es w r hOther, shares_other_write es w r u.tenant clock hOther hAdded]
    constructor
    · rintro ⟨⟨hAsks, _, hHeld⟩, hMay⟩
      exact ⟨⟨hAsks, hHeld⟩, hMay⟩
    · rintro ⟨⟨hAsks, hHeld⟩, hMay⟩
      exact ⟨⟨hAsks, trivial, hHeld⟩, hMay⟩
  · rw [records_other_write es w r hOther]
    constructor
    · rintro ⟨⟨_, _, hHeld⟩, _⟩
      exact absurd hHeld hAdded
    · rintro ⟨⟨_, hHeld⟩, _⟩
      exact absurd hHeld hAdded

end Crm.SharedCrm.Proofs
