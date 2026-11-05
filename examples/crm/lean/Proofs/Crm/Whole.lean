import FrFlowGen.Crm.Whole.Spec
import Proofs.Crm.Lemmas

/-! Crm's promises about the database's search and the screens over it hold together (owner §39): a search answering
with the stored records that match (today's `storedMatching`), changing nothing, keeps `recordsByQuery` and
`searchKeeps`; the records screen over it then keeps `readContract`, the sales screen `dealSearch`; and a user finds
what the screens return (`searches`). And today's examples of the job's store. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Whole.Proofs
open Crm

theorem consistent_5 : Obl.consistent_5 := by
  refine ⟨fun u q r w => r ∈ onScreen q (search_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1 (dealsOf_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1,
    (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)), ?_, Runs.matching_records, Runs.matching_keeps,
    Runs.read_contract (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_records Runs.matching_keeps,
    Runs.deal_search (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_records Runs.matching_keeps⟩
  intro u q r w _ _ _
  dsimp only

-- Today's examples of the job's store, each its code's run on the store given (`frflow_auto` does not decide them
-- within an example's budget).

theorem example_ExpireExamples_0 : Obl.example_ExpireExamples_0 := by
  intro _ _ _ _; simp [expireCode, ended]

theorem example_ExpireExamples_1 : Obl.example_ExpireExamples_1 := by
  intro _ _ _ _; simp [expireCode, ended]

theorem example_ExpireExamples_2 : Obl.example_ExpireExamples_2 := by
  intro _ _ _ _; simp [expireCode, ended]

theorem example_ExpireExamples_3 : Obl.example_ExpireExamples_3 := by
  intro _ _ _ _; simp [expireCode, ended]

end Crm.Whole.Proofs
