import FrFlowGen.Rebac.CheckContract.Spec

/-! Authored proofs of the obligations of CheckContract. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Rebac.CheckContract.Proofs
open Rebac.CheckContract

/-- Resolution through the two indexes gives what the tuples of the version give: by induction on the depth. Reading an
object's tuples through the store's index is reading the version's tuples about that object, and the rules through the
schema index are the schema's. -/
theorem impl : Obl.impl := by
  unfold Obl.impl
  frflow_intro
  simp only [frflow_defs] at *
  intro q v
  suffices h : ∀ (fuel : List Unit) (o : Obj) (r : String),
      resolve rulesFor tuplesOf fuel v o r q.person =
        holds schema fuel
          (List.foldl
            (fun ts w =>
              match w with
              | Write.Add t => if t ∈ ts then ts else ts ++ [t]
              | Write.Remove t_1 => List.filter (fun x => decide ¬x = t_1) ts)
            [] (List.take v.toNat writes)) o r q.person from h _ _ _
  intro fuel
  induction fuel with
  | nil => intro o r; simp [resolve, holds]
  | cons _ rest ih =>
    intro o r
    simp only [resolve, holds, h_SchemaIndex, h_StoreIndex, rulesOf, ih, List.mem_filter, decide_eq_true_eq, and_assoc]
    rfl
