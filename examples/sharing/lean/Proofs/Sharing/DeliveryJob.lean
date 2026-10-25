import FrFlowGen.Sharing.DeliveryJob.Spec

/-! Authored proofs of the obligations of DeliveryJob. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.DeliveryJob.Proofs
open Sharing.DeliveryJob

/-- With an empty outbox the run reads the store and changes nothing. Otherwise, for each case of the faults: the first
read fails; or every try at the mail server fails; or the mail server takes the notice and then reading or saving the
store fails; or all goes through. The library changes only by the notice leaving the outbox, and only after the mail
server has it. -/
theorem impl : Obl.impl := by
  unfold Obl.impl
  unfold Sharing.DeliveryJob.claim Sharing.DeliveryJob.post Sharing.DeliveryJob.failure
    Sharing.deliveryJob_run Sharing.deliveryJob
  intro w
  rcases ho : w.libraryStore.outbox with _ | ⟨n, rest⟩
  · have ht : List.take (Int.toNat 1) ([] : List Notice) = [] := rfl
    simp only [ht, frflow_defs]
    all_goals (repeat' (frflow_fault_case <;> try simp only [ho, ht, frflow_defs]))
    all_goals simp_all
  · have ht : List.take (Int.toNat 1) (n :: rest) = [n] := rfl
    simp only [ht, frflow_defs]
    all_goals (repeat' (frflow_fault_case <;> try simp only [ho, ht, frflow_defs]))
    all_goals (try split) <;> simp_all

end Sharing.DeliveryJob.Proofs
