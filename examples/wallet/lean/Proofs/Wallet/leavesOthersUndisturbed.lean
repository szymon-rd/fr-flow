import FrFlowGen.Wallet.leavesOthersUndisturbed.Spec
import Proofs.Wallet.Lemmas

/-! What a transfer relies on of other calls, each of its own steps grants them. The claim posts nothing and undoes
no claim. The move is made from books solvent and orderly in which the transfer's request is claimed (those the
claim left, or those other calls left since, which keep that); it keeps them solvent, keeps the claims, and posts
for its own request only, a request claimed, so the books stay orderly. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.leavesOthersUndisturbed.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro claim moveIfCovered hkeeps hstays hsolvent hclaims hposts books between other t hpos hpre step hstep
  obtain ⟨⟨hs, ho⟩, hne⟩ := hpre
  have s1 : solvent (claim books t.request).2 := same_postings_solvent books _ hs (hkeeps books t.request)
  have o1 : orderly (claim books t.request).2 := by
    intro p hp
    rw [hkeeps books t.request] at hp
    exact hstays books t.request p.request (Or.inr (ho p hp))
  have first : undisturbed other books (claim books t.request).2 :=
    ⟨⟨⟨s1, o1⟩, fun r hr => hstays books t.request r (Or.inr hr)⟩, by rw [hkeeps books t.request]⟩
  have mine : t.request ∈ (claim books t.request).2.claimed := hstays books t.request t.request (Or.inl rfl)
  have second : ∀ now : Books, solvent now → orderly now → t.request ∈ now.claimed →
      undisturbed other now (moveIfCovered now t).2 := by
    intro now sn on cn
    refine ⟨⟨⟨hsolvent now t hpos sn, ?_⟩, ?_⟩, hposts now other t hpos hne⟩
    · intro p hp
      rw [hclaims now t hpos]
      by_cases hreq : p.request = t.request
      · rw [hreq]
        exact cn
      · have posted : p ∈ made (moveIfCovered now t).2.postings p.request :=
          List.mem_filter.mpr ⟨hp, by simp⟩
        rw [hposts now p.request t hpos hreq] at posted
        exact on p (List.mem_filter.mp posted).1
    · intro r hr
      rw [hclaims now t hpos]
      exact hr
  unfold transferAmongOthersCode at hstep
  by_cases hmine : (claim books t.request).1
  · simp only [hmine, not_true_eq_false, ite_false, List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hstep
    rcases hstep with rfl | rfl
    · exact first
    · by_cases hothers : others t (claim books t.request).2 (Option.getD (between 2) (claim books t.request).2)
      · simp only [hothers, ite_true]
        obtain ⟨⟨⟨ss, os⟩, cs⟩, _⟩ := hothers
        exact second _ ss os (cs _ mine)
      · simp only [hothers, ite_false]
        exact second _ s1 o1 mine
  · simp only [hmine, not_false_eq_true, ite_true, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hstep
    subst hstep
    exact first

end Wallet.leavesOthersUndisturbed.Proofs
