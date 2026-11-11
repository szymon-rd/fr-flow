import FrFlowGen.Shop.leavesOthersUndisturbed.Spec
import Proofs.Shop.Lemmas

/-! What placing an order relies on of other calls, each of its own steps grants them (`Lemmas.every_step`). The
stock's steps leave no product oversold and the books alone; the journal's steps touch neither. The claim posts
nothing and undoes no claim. The charge is made from books in which the order's payment is claimed (`B`): it
keeps them solvent, keeps the claims, and posts for its own order only, so the books stay orderly. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.leavesOthersUndisturbed.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register hold settle claim chargeIfCovered putBack hhold hput hkeeps hstays hsolvent hclaims hposts
    shop between other o hpos hpre
  obtain ⟨⟨⟨hs, hv⟩, ho⟩, hne⟩ := hpre
  -- A step that leaves the books as they are and no product oversold.
  have aside : ∀ (b after : ShopState), (stocked b.stock ∧ solvent b.books ∧ orderly b.books) →
      stocked after.stock → after.books = b.books →
      undisturbed other b after ∧ (stocked after.stock ∧ solvent after.books ∧ orderly after.books) := by
    intro b after hb hst hbooks
    unfold undisturbed
    rw [hbooks]
    exact ⟨⟨⟨⟨⟨hst, hb.2.1⟩, hb.2.2⟩, fun _ hr => hr⟩, rfl⟩, hst, hb.2.1, hb.2.2⟩
  -- The claim: nothing posted, no claim undone.
  have claimed : ∀ b : ShopState, (stocked b.stock ∧ solvent b.books ∧ orderly b.books) →
      undisturbed other b { b with books := (claim b.books o.id_).2 } ∧
        (stocked b.stock ∧ solvent (claim b.books o.id_).2 ∧ orderly (claim b.books o.id_).2) := by
    intro b hb
    have sv : solvent (claim b.books o.id_).2 := same_postings_solvent b.books _ hb.2.1 (hkeeps b.books o.id_)
    have od : orderly (claim b.books o.id_).2 := by
      intro p hp
      rw [hkeeps b.books o.id_] at hp
      exact hstays b.books o.id_ p.order (Or.inr (hb.2.2 p hp))
    exact ⟨⟨⟨⟨⟨hb.1, sv⟩, od⟩, fun r hr => hstays b.books o.id_ r (Or.inr hr)⟩,
      congrArg (made · other) (hkeeps b.books o.id_)⟩, hb.1, sv, od⟩
  -- The charge, from books in which the order's payment is claimed.
  have charged : ∀ b : ShopState, (stocked b.stock ∧ solvent b.books ∧ orderly b.books) →
      o.id_ ∈ b.books.claimed →
      undisturbed other b { b with books := (chargeIfCovered b.books o).2 } ∧
        (stocked b.stock ∧ solvent (chargeIfCovered b.books o).2 ∧ orderly (chargeIfCovered b.books o).2) := by
    intro b hb mine
    have sv := hsolvent b.books o hpos hb.2.1
    have od : orderly (chargeIfCovered b.books o).2 := by
      intro p hp
      rw [hclaims b.books o hpos]
      by_cases hreq : p.order = o.id_
      · rw [hreq]
        exact mine
      · have posted : p ∈ made (chargeIfCovered b.books o).2.postings p.order :=
          List.mem_filter.mpr ⟨hp, by simp⟩
        rw [hposts b.books p.order o hpos hreq] at posted
        exact hb.2.2 p (List.mem_filter.mp posted).1
    exact ⟨⟨⟨⟨⟨hb.1, sv⟩, od⟩, fun r hr => (hclaims b.books o hpos).symm ▸ hr⟩,
      hposts b.books other o hpos hne⟩, hb.1, sv, od⟩
  exact every_step register hold settle claim chargeIfCovered putBack o between
    (fun b => stocked b.stock ∧ solvent b.books ∧ orderly b.books) (fun _ => True)
    (fun b => o.id_ ∈ b.books.claimed) (fun step => undisturbed other step.1 step.2)
    (fun _ _ _ h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩) (fun _ _ _ _ => trivial) (fun _ _ hb h => h.1.2 _ hb)
    (fun b hb _ => ⟨(aside b { b with journal := (register b.journal o.id_).2 } hb hb.1 rfl).1,
      (aside b { b with journal := (register b.journal o.id_).2 } hb hb.1 rfl).2, trivial⟩)
    (fun b hb _ => ⟨(aside b { b with stock := (hold b.stock o).2 } hb (hhold b.stock o hpos hb.1) rfl).1,
      (aside b { b with stock := (hold b.stock o).2 } hb (hhold b.stock o hpos hb.1) rfl).2, trivial⟩)
    (fun b st hb => aside b { b with journal := (settle b.journal st).2 } hb hb.1 rfl)
    (fun b hb _ => ⟨(claimed b hb).1, (claimed b hb).2, fun _ => hstays b.books o.id_ o.id_ (Or.inl rfl)⟩)
    (fun b hb mine => charged b hb mine)
    (fun b hb => aside b { b with stock := (putBack b.stock o).2 } hb (hput b.stock o hpos hb.1) rfl)
    shop ⟨hs, hv, ho⟩ trivial

end Shop.leavesOthersUndisturbed.Proofs
