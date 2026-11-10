import FrFlowGen.Wallet.postsOnlyOnceClaimed.Spec
import Proofs.Wallet.Lemmas

/-! A transfer that finds its request claimed loses its claim, and its one step, the claim, posts nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.postsOnlyOnceClaimed.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro claim moveIfCovered hkeeps hwon books between t _ hclaimed step hstep
  have lost : ¬(claim books t.request).1 := fun won => ((hwon books t.request).mp won) hclaimed
  unfold transferAmongOthersCode at hstep
  simp only [lost, not_false_eq_true, ite_true, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hstep
  subst hstep
  exact hkeeps books t.request

end Wallet.postsOnlyOnceClaimed.Proofs
