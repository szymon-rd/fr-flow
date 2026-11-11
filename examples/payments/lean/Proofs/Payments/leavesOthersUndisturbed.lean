import FrFlowGen.Payments.leavesOthersUndisturbed.Spec
import Proofs.Payments.Lemmas

/-! What handling a payment relies on of other calls, each of its own steps grants them (`Lemmas.every_step`).
The assessment leaves no card over its limit and every payment decided as it was; the posting leaves the books
orderly and every payment posted; the commit touches neither. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.leavesOthersUndisturbed.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro assess postOnce advance hlimits hdecisions hposted horderly pipeline between other p hstart
  exact every_step assess postOnce advance p between
    (fun b => withinLimits b.spending ∧ orderly b.books) (fun b => withinLimits b.spending ∧ orderly b.books)
    (fun _ b => withinLimits b.spending ∧ orderly b.books)
    (fun step => undisturbed other step.1 step.2)
    (fun _ _ _ _ h => h.1.1) (fun _ _ _ h => h.1.1)
    (fun b hb => ⟨⟨⟨⟨hlimits b.spending p hb.1, hb.2⟩, or_of_imp (hdecisions b.spending other p)⟩,
      or_of_imp id⟩, hlimits b.spending p hb.1, hb.2⟩)
    (fun _ b _ hb => ⟨⟨⟨⟨hb.1, horderly b.books p hb.2⟩, or_of_imp (fun was => ⟨was, rfl⟩)⟩,
      or_of_imp (hposted b.books other p)⟩, hb.1, horderly b.books p hb.2⟩)
    (fun _ _ _ hb => hb)
    (fun _ hb => ⟨⟨hb, or_of_imp (fun was => ⟨was, rfl⟩)⟩, or_of_imp id⟩)
    pipeline hstart

end Payments.leavesOthersUndisturbed.Proofs
