import FrFlowGen.Shop.neverOversold.Spec
import Proofs.Shop.Lemmas

/-! No product is oversold at any step (`Lemmas.every_step`): other calls leave none oversold, a hold is made only of
units there are, units put back only add, and the other steps do not touch the stock. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.neverOversold.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register hold settle claim chargeIfCovered putBack hhold hput shop between o hpos hstocked
  exact every_step register hold settle claim chargeIfCovered putBack o between
    (fun b => stocked b.stock) (fun _ => True) (fun _ => True) (fun step => stocked step.2.stock)
    (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ hb _ => ⟨hb, hb, trivial⟩)
    (fun b hb _ => ⟨hhold b.stock o hpos hb, hhold b.stock o hpos hb, trivial⟩)
    (fun _ _ hb => ⟨hb, hb⟩)
    (fun _ hb _ => ⟨hb, hb, fun _ => trivial⟩)
    (fun _ hb _ => ⟨hb, hb⟩)
    (fun b hb => ⟨hput b.stock o hpos hb, hput b.stock o hpos hb⟩)
    shop hstocked trivial

end Shop.neverOversold.Proofs
