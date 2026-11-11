import FrFlowGen.Payments.postedOnce.Spec
import Proofs.Payments.Lemmas

/-! No step adds to the postings of a payment that has some (`Lemmas.every_step`). Only the posting touches the
books; it is made from orderly books (those the call started from, or those other calls left), where the ledger
adds nothing to a payment posted; and it leaves them orderly. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.postedOnce.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro assess postOnce advance horderly hadds pipeline between id p hstart
  exact every_step assess postOnce advance p between
    (fun b => orderly b.books) (fun b => orderly b.books) (fun _ b => orderly b.books)
    (fun step => made step.1.books.postings id = [] ∨
      made step.2.books.postings id = made step.1.books.postings id)
    (fun _ _ _ _ h => h.1.1.2) (fun _ _ _ h => h.1.1.2)
    (fun _ hb => ⟨Or.inr rfl, hb⟩)
    (fun _ b _ hb => ⟨hadds b.books id p hb, horderly b.books p hb⟩)
    (fun _ _ _ hb => hb)
    (fun _ _ => Or.inr rfl)
    pipeline hstart

end Payments.postedOnce.Proofs
