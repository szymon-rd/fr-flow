import FrFlowGen.Wallet.sentAgainChangesNothing.Spec
import Proofs.Wallet.Lemmas

/-! A transfer sent again changes nothing: the first call left its request claimed (the claim marks it, the move
keeps the claims), so the second call's claim is lost, and a lost claim leaves the books as they are. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.sentAgainChangesNothing.Proofs
open Wallet Wallet.Lemmas

/-- A transfer whose claim is lost leaves the books as its claim left them. -/
theorem lost_leaves (claim : Books → String → (Prop × Books))
    (moveIfCovered : Books → Transfer → (Prop × Books)) (books : Books) (t : Transfer)
    (lost : ¬(claim books t.request).1) :
    (transferCode claim moveIfCovered books t).2 = (claim books t.request).2 := by
  unfold transferCode
  simp only [lost, not_false_eq_true, ite_true]

theorem impl : Obl.impl := by
  intro claim moveIfCovered hwon hstays hlost hclaims books t hpos
  have marked : t.request ∈ (transferCode claim moveIfCovered books t).2.claimed := by
    unfold transferCode
    by_cases hmine : (claim books t.request).1
    · simp only [hmine, not_true_eq_false, ite_false]
      rw [hclaims _ t hpos]
      exact hstays books t.request t.request (Or.inl rfl)
    · simp only [hmine, not_false_eq_true, ite_true]
      exact hstays books t.request t.request (Or.inl rfl)
  have lost : ¬(claim (transferCode claim moveIfCovered books t).2 t.request).1 :=
    fun won => ((hwon _ t.request).mp won) marked
  rw [lost_leaves claim moveIfCovered _ t lost]
  exact hlost _ t.request lost

end Wallet.sentAgainChangesNothing.Proofs
