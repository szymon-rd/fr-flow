import FrFlowGen.Crm.Whole.Spec
import Proofs.Crm.Lemmas

/-! Crm's promises about the database's search and the screens over it hold together (owner §39): a search answering
with the stored records that match (today's `storedMatching`), changing nothing, keeps `fetchesOnlyMatches`,
`fetchesEveryMatch` and `searchKeeps`; the records screen over it then keeps `readContract`'s parts, the sales screen
`dealSearch`'s; and a user finds what the screens return (`searches`). And today's examples of the job's store. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Whole.Proofs
open Crm

theorem consistent_3 : Obl.consistent_3 := by
  refine ⟨fun u q r w => r ∈ onScreen q (search_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1 (dealsOf_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1,
    (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)), ?_, Runs.matching_only, Runs.matching_every, Runs.matching_keeps,
    Runs.reads_only_matching (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.reads_only_readable (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.reads_all_readable (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.deals_only_matching (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.deals_only_deals (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.deals_only_readable (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps,
    Runs.deals_all_readable (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_only Runs.matching_every Runs.matching_keeps⟩
  intro u q r w _ _ _
  dsimp only

-- Today's examples of the job's store, each its code's run on the store given (`frflow_auto` does not decide them
-- within an example's budget).

theorem example_ExpireExamples_0 : Obl.example_ExpireExamples_0 := by
  intro _ _ _ _; simp [expireCode, ended, liveShares, liveExpiries]

theorem example_ExpireExamples_1 : Obl.example_ExpireExamples_1 := by
  intro _ _ _ _; simp [expireCode, ended, liveShares, liveExpiries]

theorem example_ExpireExamples_2 : Obl.example_ExpireExamples_2 := by
  intro _ _ _ _; simp [expireCode, ended, liveShares, liveExpiries]

theorem example_ExpireExamples_3 : Obl.example_ExpireExamples_3 := by
  intro _ _ _ _; simp [expireCode, ended, liveShares, liveExpiries]

end Crm.Whole.Proofs
