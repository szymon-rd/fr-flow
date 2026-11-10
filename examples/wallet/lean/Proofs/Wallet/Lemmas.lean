import FrFlowGen.Wallet.Domain

/-! What the proofs of the wallet share: an account's balance over postings added, and what solvent and orderly
books give. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.Lemmas
open Wallet

/-- A sum of postings' amounts from `z` is `z` and their sum from nothing. -/
theorem sum_from (l : List Posting) (z : Int) :
    List.foldl (fun (sum : Int) (p : Posting) => sum + p.amount) z l =
      z + List.foldl (fun (sum : Int) (p : Posting) => sum + p.amount) 0 l := by
  induction l generalizing z with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (z + p.amount), ih (0 + p.amount)]
    omega

/-- An account's balance over postings added is its balance before and its balance in those added. -/
theorem balance_append (l m : List Posting) (a : String) : balance (l ++ m) a = balance l a + balance m a := by
  unfold balance
  rw [List.filter_append, List.foldl_append, sum_from]

/-- What a transfer's two postings change of an account's balance. -/
theorem balance_moved (t : Transfer) (a : String) :
    balance [Posting.mk t.request t.«from» ((0 : Int) - t.amount), Posting.mk t.request t.to t.amount] a =
      (if t.«from» = a then -t.amount else 0) + (if t.to = a then t.amount else 0) := by
  unfold balance
  by_cases h1 : t.«from» = a <;> by_cases h2 : t.to = a <;> simp [List.filter, h1, h2]

/-- In solvent books every account's balance is at least nothing, those with no posting too. -/
theorem balance_nonneg (b : Books) (h : solvent b) (a : String) : 0 ≤ balance b.postings a := by
  by_cases hex : ∃ p ∈ b.postings, p.account = a
  · obtain ⟨p, hp, rfl⟩ := hex
    exact h p hp
  · have none : List.filter (fun p => decide (p.account = a)) b.postings = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      simp only [decide_eq_true_eq]
      exact fun h' => hex ⟨p, hp, h'⟩
    unfold balance
    rw [none]
    simp

/-- Books whose postings are solvent books' and a covered transfer's two are solvent. -/
theorem moved_solvent (b after : Books) (t : Transfer) (hpos : 0 < t.amount) (h : solvent b)
    (hc : t.amount ≤ balance b.postings t.«from»)
    (hp : after.postings = b.postings ++
      [Posting.mk t.request t.«from» ((0 : Int) - t.amount), Posting.mk t.request t.to t.amount]) :
    solvent after := by
  intro p _
  rw [hp, balance_append, balance_moved]
  have held := balance_nonneg b h p.account
  by_cases h1 : t.«from» = p.account <;> by_cases h2 : t.to = p.account <;> simp only [h1, h2, ite_true, ite_false]
  all_goals first
    | (rw [h1] at hc; omega)
    | omega

/-- Books with solvent books' postings are solvent. -/
theorem same_postings_solvent (b after : Books) (h : solvent b) (hp : after.postings = b.postings) :
    solvent after := by
  intro p hm
  rw [hp] at hm ⊢
  exact h p hm

/-- In orderly books a request not claimed has no posting. -/
theorem unclaimed_unmade (b : Books) (h : orderly b) (r : String) (hr : r ∉ b.claimed) : made b.postings r = [] := by
  unfold made
  rw [List.filter_eq_nil_iff]
  intro p hp
  simp only [decide_eq_true_eq]
  exact fun h' => hr (h' ▸ h p hp)

end Wallet.Lemmas
