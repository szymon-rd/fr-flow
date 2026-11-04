import FrFlowGen.Sharing.deliveryJob.Spec
import Proofs.Sharing.Lemmas

/-! A run of delivery, notice by notice (`Lemmas.mapM_along`): each send leaves the mail server's mailbox of its
person as it was or with the notice taken, and the notice leaves the outbox only once the mail server has it, in one
transaction; the oldest notices of an outbox are of different people, so no send touches another's mailbox. A run that
loses its race with the time limit is cancelled between two of its steps, each notice's delivery at its own (each step
the scheduler's choice, `FrFlow.Races.step`): what it did until then is one of what a delivery does, so it keeps the
same; one whose outbox cannot be read changes neither. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.deliveryJob.Proofs
open Sharing


set_option maxHeartbeats 4000000 in
theorem impl : Obl.impl := by
  unfold Obl.impl
  exact Lemmas.delivery_job

/-- Two notices of the outbox's first ones sent at once, each with its own faults, commute: one notice, or two
people's mailboxes (`Lemmas.sends_commute`). The sleeps at once commute as FrFlow's automation shows. -/
theorem commute_2 : Obl.commute_2 := by
  unfold Obl.commute_2
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ h
  exact Lemmas.sends_commute n₁ n₂ (Lemmas.firstOfEach_apart _ _ _ h) w f₁ r₁ f₂ r₂ t₁ t₂

/-- Two removals from the outbox at once, each a transaction with its own faults, commute
(`Lemmas.removals_commute`). -/
theorem commute_6 : Obl.commute_6 := by
  unfold Obl.commute_6
  intro r start n₁ n₂ w f₁ r₁ t₁ f₂ r₂ t₂ _
  exact Lemmas.removals_commute n₁ n₂ w f₁ r₁ f₂ r₂ t₁ t₂

end Sharing.deliveryJob.Proofs
