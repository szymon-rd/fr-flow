import FrFlowGen.Shop.doneChargePays.Spec
import Proofs.Shop.Lemmas

/-! A charge is done only when its claim was won and the ledger moved the amount; the claim posts nothing, so the
balances the move starts from are those the charge started from. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.doneChargePays.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro claim chargeIfCovered hkeeps hmoves books account o hpos hdone
  unfold chargeCode at hdone ⊢
  by_cases hmine : (claim books o.id_).1
  · by_cases hpaid : (chargeIfCovered (claim books o.id_).2 o).1
    · simp only [hmine, hpaid, not_true_eq_false, ite_true, ite_false]
      rw [hmoves _ account o hpos hpaid, hkeeps books o.id_]
    · simp [hmine, hpaid] at hdone
  · simp [hmine] at hdone

end Shop.doneChargePays.Proofs
