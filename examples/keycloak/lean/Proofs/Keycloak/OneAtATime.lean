import FrFlowGen.Keycloak.OneAtATime.Spec

/-! Authored proof that OneAtATime refines Sessions: every store reached has distinct tokens, by
induction over the requests (`FrFlow.always`), and each request does only what it asks and is
granted, since the store after `rs ++ [q]` is `q` applied to the store after `rs`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.OneAtATime.Proofs
open Keycloak.OneAtATime

theorem link : Obl.link := by
  unfold Obl.link
  intro Store Request distinct initial onlyThat granted m h
  simp only [frflow_defs] at *
  obtain ⟨h0, hs⟩ := h
  constructor
  · intro rs
    exact FrFlow.always m distinct initial h0 (fun s q hd => (hs s q).1.1 hd) rs
  · intro rs q
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨(hs _ q).1.2, (hs _ q).2⟩

/-- The root says something here: with no store having distinct tokens, no model meets it. -/
theorem nontrivial : Obl.nontrivial := by
  unfold Obl.nontrivial
  exact ⟨Unit, Unit, fun _ => False, (), fun _ _ _ => True, fun _ _ _ => True, fun s _ => s, by simp [frflow_defs]⟩

end Keycloak.OneAtATime.Proofs
