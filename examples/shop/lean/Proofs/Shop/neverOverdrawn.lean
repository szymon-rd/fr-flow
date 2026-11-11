import FrFlowGen.Shop.neverOverdrawn.Spec
import Proofs.Shop.Lemmas

/-! No account is overdrawn at any step (`Lemmas.every_step`): other calls leave none overdrawn, a claim posts
nothing, a charge is made only when covered, and the other steps do not touch the books. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.neverOverdrawn.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register hold settle claim chargeIfCovered putBack hkeeps hsolvent shop between o hpos hstart
  have claimed : ∀ b : ShopState, solvent b.books → solvent (claim b.books o.id_).2 :=
    fun b hb => same_postings_solvent b.books _ hb (hkeeps b.books o.id_)
  exact every_step register hold settle claim chargeIfCovered putBack o between
    (fun b => solvent b.books) (fun _ => True) (fun _ => True) (fun step => solvent step.2.books)
    (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ hb _ => ⟨hb, hb, trivial⟩)
    (fun _ hb _ => ⟨hb, hb, trivial⟩)
    (fun _ _ hb => ⟨hb, hb⟩)
    (fun b hb _ => ⟨claimed b hb, claimed b hb, fun _ => trivial⟩)
    (fun b hb _ => ⟨hsolvent b.books o hpos hb, hsolvent b.books o hpos hb⟩)
    (fun _ hb => ⟨hb, hb⟩)
    shop hstart trivial

end Shop.neverOverdrawn.Proofs
