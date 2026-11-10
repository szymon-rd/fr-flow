import FrFlowGen.Wallet.carriedOutOnce.Spec
import Proofs.Wallet.Lemmas

/-! No step of a transfer adds to the postings of a request already made. The claim posts nothing. The move posts
for the transfer's own request only, and is reached only by the call that won the claim: the request was not
claimed, so in orderly books it had no posting, and other calls, which leave a request's postings to the call that
claimed it (`undisturbed`), made none since. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.carriedOutOnce.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro claim moveIfCovered hkeeps hwon hposts books between request t hpos hord step hstep
  have claimed : made (claim books t.request).2.postings request = made books.postings request := by
    rw [hkeeps books t.request]
  unfold transferAmongOthersCode at hstep
  by_cases hmine : (claim books t.request).1
  · simp only [hmine, not_true_eq_false, ite_false, List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hstep
    rcases hstep with rfl | rfl
    · exact Or.inr claimed
    · by_cases hreq : request = t.request
      · refine Or.inl ?_
        have unclaimed : t.request ∉ books.claimed := (hwon books t.request).mp hmine
        have none : made (claim books t.request).2.postings t.request = [] := by
          rw [hkeeps books t.request]
          exact unclaimed_unmade books hord t.request unclaimed
        subst hreq
        by_cases hothers : others t (claim books t.request).2 (Option.getD (between 2) (claim books t.request).2)
        · simp only [hothers, ite_true]
          rw [hothers.2, none]
        · simp only [hothers, ite_false]
          exact none
      · exact Or.inr (hposts _ request t hpos hreq)
  · simp only [hmine, not_false_eq_true, ite_true, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hstep
    subst hstep
    exact Or.inr claimed

end Wallet.carriedOutOnce.Proofs
