import FrFlowGen.Payments.moneyIsConserved.Spec
import Proofs.Payments.Lemmas

/-! Only the posting touches the books, and it leaves their total as it was (`Lemmas.every_step`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.moneyIsConserved.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro assess postOnce advance htotal pipeline between p
  exact every_step assess postOnce advance p between
    (fun _ => True) (fun _ => True) (fun _ _ => True)
    (fun step => total step.2.books.postings = total step.1.books.postings)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ => ⟨rfl, trivial⟩)
    (fun _ b _ _ => ⟨htotal b.books p, trivial⟩)
    (fun _ _ _ _ => trivial)
    (fun _ _ => rfl)
    pipeline trivial

end Payments.moneyIsConserved.Proofs
