import Lean

/-!
`frflow_faults`: a run of a flow that may fail matches on the world's faults, one call of a failing
boundary at a time. The tactic takes each case in turn: the faults it matches on are empty, or a
fault (`true`: the call fails, `false`: it does not) then the rest, and so on for the rest, until
no match on faults is left; each case's run is then computed by `simp`.
-/

namespace FrFlow
open Lean Elab Tactic Meta

/-- The subterms of `e` outside binders: where a match's discriminant is. -/
private partial def subterms (e : Expr) : List Expr :=
  e :: match e with
    | .app f a => subterms f ++ subterms a
    | .mdata _ b => subterms b
    | .proj _ _ b => subterms b
    | _ => []

/-- One case split on faults: the first list of faults the goal matches on, empty or a fault then the rest. -/
elab "frflow_fault_case" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let listBool ← mkAppM ``List #[mkConst ``Bool]
  let isFaults (t : Expr) : MetaM Bool := do
    if t.hasLooseBVars || t.hasMVar || t.isAppOf ``List.cons || t.isAppOf ``List.nil then return false
    if !(t.isFVar || (t.getAppFn.isConst && t.getAppNumArgs ≥ 1) || t.isProj) then return false
    try isDefEq (← inferType t) listBool catch _ => return false
  let some t ← (subterms goal).findM? (fun t => liftM (isFaults t)) | throwError "frflow_fault_case: no faults to split on"
  let s ← Term.exprToSyntax t
  if t.isFVar then
    evalTactic (← `(tactic| rcases $s:term with _ | ⟨_ | _, faults⟩))
  else
    evalTactic (← `(tactic| (generalize _hfaults : $s = faults at *; rcases faults with _ | ⟨_ | _, faults⟩)))
  -- A split that left a goal as it was (the faults could not be abstracted) is no progress: stop here.
  for g in ← getGoals do
    if (← instantiateMVars (← g.getType)) == goal then throwError "frflow_fault_case: the split made no progress"

/-- Every case of the faults a run takes, each computed. -/
macro "frflow_faults" : tactic => `(tactic| (intros; repeat (frflow_fault_case <;> try simp only [] at *)))

end FrFlow
