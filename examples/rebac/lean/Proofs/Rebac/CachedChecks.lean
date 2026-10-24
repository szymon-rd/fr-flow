import FrFlowGen.Rebac.CachedChecks.Spec

/-! Authored proofs of the obligations of CachedChecks. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Rebac.CachedChecks.Proofs
open Rebac.CachedChecks

theorem impl : Obl.impl := by
  unfold Obl.impl
  frflow_intro
  simp only [frflow_defs] at *
  intro a w hs
  rcases Option.eq_none_or_eq_some (List.find? (fun c => decide (c.ask = a)) w.answerCache) with hf | ⟨c, hf⟩
  rotate_left
  ·
    -- a hit: the kept answer is the check's, and the cache is unchanged
    have hask : c.ask = a := by simpa using List.find?_some hf
    have hmem : c ∈ w.answerCache := List.mem_of_find?_eq_some hf
    simp only [hf, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, Option.getD_some, FrFlow.runOn_pure]
    exact ⟨hask ▸ hs c hmem, hs⟩
  ·
    -- a miss: the check's answer, kept in front of the others
    simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte, FrFlow.runOn_bind, FrFlow.runOn_within, FrFlow.runOn_modify,
      FrFlow.runOn_pure]
    refine ⟨trivial, fun c hc => ?_⟩
    have hc' := List.mem_of_mem_take hc
    simp only [List.mem_cons, List.mem_filter] at hc'
    rcases hc' with rfl | ⟨hin, _⟩
    · rfl
    · exact hs c hin
