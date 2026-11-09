import FrFlowGen.Sharing.failedDeliveryChangesNothing.Spec
import Proofs.Sharing.Lemmas

/-! A run of delivery whose outbox cannot be read changes neither the library nor the mail server: what deliveryJob says of a run that fails (`Lemmas.delivery_job`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.failedDeliveryChangesNothing.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl Sharing.failedDeliveryChangesNothing.claim
  intro w g0 g1 g2 g3 g4 g5 g6
  have h := Lemmas.delivery_job w g0 g1 g2 g3 g4 g5 g6
  revert h
  cases delivery_run w with
  | mk res after =>
    cases res with
    | error e => intro h; exact ⟨trivial, h.2⟩
    | ok u => intro h; exact ⟨trivial, trivial⟩

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

end Sharing.failedDeliveryChangesNothing.Proofs
