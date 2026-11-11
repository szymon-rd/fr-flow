import FrFlowGen.Shop.duplicateDoesNothing.Spec
import Proofs.Shop.Lemmas

/-! A call that finds its order registered loses the registration, and its one step, the registration, leaves the
journal as it is. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.duplicateDoesNothing.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register hold settle claim chargeIfCovered putBack hwon hlost shop between o _ hreg step hstep
  have lost : ¬(register shop.journal o.id_).1 := fun won => ((hwon shop.journal o.id_).mp won) hreg
  unfold placeAmongOthersCode at hstep
  extract_lets did s1 tr1 mine seen2 n2 did1 s2 tr2 reserved seen3 n3 didR sR trR did2 s3 tr3 won seen4 n4 did3
    s4 tr4 paid afterP charged seen5 n5 didC sC trC didB s5 tr5 seen6 n6 did6 s6 tr6 after1 after2 after3 at hstep
  have lost' : ¬mine := lost
  simp only [after3, lost', not_false_eq_true, ite_true, tr1, List.nil_append, List.mem_singleton] at hstep
  subst hstep
  show ({ shop with journal := (register shop.journal o.id_).2 } : ShopState) = shop
  rw [hlost shop.journal o.id_ lost]

end Shop.duplicateDoesNothing.Proofs
