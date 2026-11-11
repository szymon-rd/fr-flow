import FrFlowGen.Shop.chargedOnce.Spec
import Proofs.Shop.Lemmas

/-! No step adds to the postings of an order already charged (`Lemmas.every_step`). Only the charge posts, and
only for its own order. It is reached only by the call that won the payment's claim: the payment was not claimed,
so in orderly books the order had no posting, and other calls, which leave an order's postings to the call that
claimed its payment (`undisturbed`), made none since. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.chargedOnce.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register hold settle claim chargeIfCovered putBack hkeeps hwon hposts shop between order o hpos hord
  exact every_step register hold settle claim chargeIfCovered putBack o between
    (fun _ => True) (fun b => orderly b.books) (fun b => made b.books.postings o.id_ = [])
    (fun step => made step.1.books.postings order = [] ∨
      made step.2.books.postings order = made step.1.books.postings order)
    (fun _ _ _ _ => trivial) (fun _ _ _ h => h.1.1.2) (fun _ _ hb h => h.2.trans hb)
    (fun _ _ ha => ⟨Or.inr rfl, trivial, ha⟩)
    (fun _ _ ha => ⟨Or.inr rfl, trivial, ha⟩)
    (fun _ _ _ => ⟨Or.inr rfl, trivial⟩)
    (fun b _ ha => ⟨Or.inr (congrArg (made · order) (hkeeps b.books o.id_)), trivial, fun won =>
      (congrArg (made · o.id_) (hkeeps b.books o.id_)).trans
        (unclaimed_unmade b.books ha o.id_ ((hwon b.books o.id_).mp won))⟩)
    (fun b _ hb => ⟨by
      by_cases hreq : order = o.id_
      · exact Or.inl (hreq ▸ hb)
      · exact Or.inr (hposts b.books order o hpos hreq), trivial⟩)
    (fun _ _ => ⟨Or.inr rfl, trivial⟩)
    shop trivial hord

end Shop.chargedOnce.Proofs
