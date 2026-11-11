import FrFlowGen.Payments.neverCommitsAhead.Spec
import Proofs.Payments.Lemmas

/-! Only the last step touches the position (`Lemmas.every_step`), and it moves it only from the payment's offset
to one past it. By then the payment is applied: it was decided, and other calls leave it decided as it was; if it
was approved this call posted it, and other calls leave it posted; if it was declined the record still says so.
So whichever step a crash follows, the position is not past a payment that is not applied. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.neverCommitsAhead.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro assess postOnce advance hrecorded hmarked hmoves hstays pipeline between p
  exact every_step assess postOnce advance p between
    (fun _ => True) (fun b => applied b p.id_)
    (fun answer b => decided b.spending p.id_ ∧ (answer = approved b.spending p.id_))
    (fun step => step.2.committed = step.1.committed ∨
      ((step.1.committed = p.offset ∧ step.2.committed = p.offset + 1) ∧ applied step.2 p.id_))
    (fun _ _ _ hb h => (h.1.2.resolve_left (fun not => not hb.1)).elim
      (fun still same => ⟨still, hb.2.trans same.symm⟩))
    (fun _ _ hb h => by
      have still := h.1.2.resolve_left (fun not => not hb.1)
      refine ⟨still.1, hb.2.elim (fun declined => Or.inl (fun app => declined (still.2.mp app)))
        (fun posted => Or.inr (h.2.resolve_left (fun not => not posted)))⟩)
    (fun b _ => ⟨Or.inl rfl, hrecorded b.spending p⟩)
    (fun _ b _ hb => ⟨Or.inl rfl, hb.1, Or.inr (hmarked b.books p)⟩)
    (fun _ _ declined hb => ⟨hb.1, Or.inl (fun app => declined (hb.2.mpr app))⟩)
    (fun b hb => by
      by_cases hat : b.committed = p.offset
      · exact Or.inr ⟨⟨hat, hmoves b.committed p.offset hat⟩, hb⟩
      · exact Or.inl (hstays b.committed p.offset hat))
    pipeline trivial

end Payments.neverCommitsAhead.Proofs
