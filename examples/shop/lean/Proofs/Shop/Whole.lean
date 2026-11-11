import FrFlowGen.Shop.Whole.Spec
import Proofs.Shop.Lemmas

/-! The conditions of the shop's claims FrFlow's search found no values for, each shown to hold of a warehouse
with five units of tea, books in which Ann holds 100, and her order of two units for 30. And the shop's examples,
each its code's run on the shop and the schedule given (FrFlow's automation does not decide them within an
example's budget): the last two, the race for the one unit of tea, in which Bob's order is placed between two steps of
Ann's, who is then answered out of stock, with no product oversold and nothing charged to her at any step. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Shop.Whole.Proofs
open Shop

theorem satisfiable_1_heldUnitsAreTaken : Obl.satisfiable_1_heldUnitsAreTaken :=
  ⟨(Stock.mk [Movement.mk "delivery" "tea" 5]), "tea", (Order.mk "o1" "ann" "tea" 2 30),
    by simp [ordersAreSensible, holdCode, available]⟩

theorem satisfiable_1_releaseUndoesReserve : Obl.satisfiable_1_releaseUndoesReserve :=
  ⟨(Stock.mk [Movement.mk "delivery" "tea" 5]), "tea", (Order.mk "o1" "ann" "tea" 2 30),
    by simp [ordersAreSensible, reserveCode, holdCode, available]⟩

theorem satisfiable_1_chargeMovesTheAmount : Obl.satisfiable_1_chargeMovesTheAmount :=
  ⟨(Books.mk [Posting.mk "top-up" "ann" 100] ["top-up"]), "ann", (Order.mk "o1" "ann" "tea" 2 30),
    by simp [ordersAreSensible, chargeIfCoveredCode, balance]⟩

theorem satisfiable_1_doneChargePays : Obl.satisfiable_1_doneChargePays :=
  ⟨(Books.mk [Posting.mk "top-up" "ann" 100] ["top-up"]), "ann", (Order.mk "o1" "ann" "tea" 2 30),
    by simp [ordersAreSensible, chargeCode, claimCode, chargeIfCoveredCode, balance]⟩

theorem satisfiable_1_confirmedIsPaid : Obl.satisfiable_1_confirmedIsPaid :=
  ⟨ShopState.mk (Stock.mk [Movement.mk "delivery" "tea" 5])
      (Books.mk [Posting.mk "top-up" "ann" 100] ["top-up"]) (Journal.mk [] []), "ann", (Order.mk "o1" "ann" "tea" 2 30), by
    simp [ordersAreSensible, placeCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode,
      chargeIfCoveredCode, available, balance]⟩

theorem satisfiable_1_duplicateDoesNothing : Obl.satisfiable_1_duplicateDoesNothing :=
  ⟨ShopState.mk (Stock.mk []) (Books.mk [] []) (Journal.mk ["o1"] []), fun _ => none, (Order.mk "o1" "ann" "tea" 2 30),
    by simp [ordersAreSensible]⟩

theorem example_ShopExamples_0 : Obl.example_ShopExamples_0 := by
  intro _ _ _ _ _ _ _ _
  simp [placeCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode, chargeIfCoveredCode,
    releaseCode, putBackCode, available, balance]

theorem example_ShopExamples_1 : Obl.example_ShopExamples_1 := by
  intro _ _ _ _ _ _ _ _
  simp [placeCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode, chargeIfCoveredCode,
    releaseCode, putBackCode, available, balance]

theorem example_ShopExamples_2 : Obl.example_ShopExamples_2 := by
  intro _ _ _ _ _ _ _ _
  simp [placeCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode, chargeIfCoveredCode,
    releaseCode, putBackCode, available, balance]

theorem example_ShopExamples_3 : Obl.example_ShopExamples_3 := by
  intro _ _ _ _ _ _ _ _
  simp [placeCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode, chargeIfCoveredCode,
    releaseCode, putBackCode, available, balance]

theorem example_ShopExamples_4 : Obl.example_ShopExamples_4 := by
  intro _ _ _
  simp [forgetfulCode, registerCode, reserveCode, holdCode, settleCode, chargeCode, claimCode,
    chargeIfCoveredCode, available, balance]

theorem example_ShopExamples_5 : Obl.example_ShopExamples_5 := by
  intro _ _ _ _ _ _
  simp [placeAmongOthersCode, registerCode, holdCode, settleCode, claimCode, chargeIfCoveredCode, putBackCode,
    others, undisturbed, stocked, solvent, orderly, made, available, balance]

theorem example_ShopExamples_6 : Obl.example_ShopExamples_6 := by
  intro _ _ _ _ _ _
  simp [placeAmongOthersCode, registerCode, holdCode, settleCode, claimCode, chargeIfCoveredCode, putBackCode,
    others, undisturbed, stocked, solvent, orderly, made, available, balance]

end Shop.Whole.Proofs
