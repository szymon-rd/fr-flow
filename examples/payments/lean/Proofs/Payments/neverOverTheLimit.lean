import FrFlowGen.Payments.neverOverTheLimit.Spec
import Proofs.Payments.Lemmas

/-! No card is over its limit at any step (`Lemmas.every_step`): other calls leave none over, an assessment
approves only what fits, and the other steps do not touch the spending. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.neverOverTheLimit.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro assess postOnce advance hkeeps pipeline between p hstart
  exact every_step assess postOnce advance p between
    (fun b => withinLimits b.spending) (fun b => withinLimits b.spending) (fun _ b => withinLimits b.spending)
    (fun step => withinLimits step.2.spending)
    (fun _ _ _ _ h => h.1.1.1) (fun _ _ _ h => h.1.1.1)
    (fun b hb => ⟨hkeeps b.spending p hb, hkeeps b.spending p hb⟩)
    (fun _ _ _ hb => ⟨hb, hb⟩)
    (fun _ _ _ hb => hb)
    (fun _ hb => hb)
    pipeline hstart

end Payments.neverOverTheLimit.Proofs
