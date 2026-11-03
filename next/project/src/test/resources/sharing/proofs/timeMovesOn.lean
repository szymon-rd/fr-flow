import FrFlowGen.Sharing.timeMovesOn.Spec
import Proofs.Sharing.Lemmas

/-! Time never goes back: a moment passed stays passed. The world's own step (`elapse`) moves the time by none or
more, where the schedule allows; a run of delivery moves it only forwards (`Lemmas.run_clock`: its tick and its
waits' ends). Its steps at once commute as deliveryJob's do. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.timeMovesOn.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro t w g1 _ _ ht
  refine ⟨fun x => ?_, ?_⟩
  · simp only [ClockModel.elapse_run, ClockModel.Ops.elapse_onWorld, FrFlow.runOn_guard, FrFlow.runOn_within,
      ClockModel.elapse, FrFlow.runOn_bind, FrFlow.runOn_get, FrFlow.runOn_set]
    have hle := FrFlow.Clock.move_le (fun w : World => w.clockModel) (fun (w : World) s => { w with clockModel := s })
      (fun w s => housekeepingOnTime s w.housekeptModel)
      (if (0 : Int) ≤ x then w.clockModel + x else w.clockModel) w (fun _ _ => rfl) (by split <;> omega)
    apply propext
    constructor
    · intro _; exact ht
    · intro _; exact Int.le_trans ht hle
  · have hc := Lemmas.run_clock w (by simp only [housekeptLately] at g1; omega)
    revert hc
    cases delivery_run w with
    | mk res after =>
      intro hc
      obtain ⟨_, h2, _⟩ := hc
      simp only at h2
      have e : (t ≤ after.clockModel) = (t ≤ w.clockModel) := propext ⟨fun _ => ht, fun _ => Int.le_trans ht h2⟩
      cases res with
      | error _ => exact ⟨trivial, e⟩
      | ok _ => exact ⟨e, trivial⟩

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

end Sharing.timeMovesOn.Proofs
