import FrFlowGen.Payments.eagerStartsWithTheCommit.Spec
import Proofs.Payments.Lemmas

/-! The eager processor's steps are its commit, its assessment, and its posting if the payment is approved: at least
the first two. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.eagerStartsWithTheCommit.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro advance assess postOnce _ _ _ _ _ _ _ _ _ _ _ _ _ pipeline between p
  unfold eagerAmongOthersCode
  extract_lets did s1 tr1 seen2 n2 did1 s2 tr2 approved seen3 n3 did2 s3 tr3 after
  by_cases happ : approved
  · simp [after, happ, tr3]
  · simp [after, happ, tr2]

end Payments.eagerStartsWithTheCommit.Proofs
