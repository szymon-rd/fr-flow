import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Intro

/-!
`frflow_intro`: introduces every binder of the goal by the name FrFlow generated for it: the open
terms by their own names, and each part's hypothesis as `h_<Part>`. A proof that refers to them by
name, not by position, still reads them right after a part or a term is added.
-/

open Lean Elab Tactic Meta in
elab "frflow_intro" : tactic => liftMetaTactic fun g => do
  let t ← whnfD (← instantiateMVars (← g.getType))
  let (_, g) ← g.introNP (getIntrosSize t)
  return [g]
