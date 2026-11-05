import Lean.Elab.Tactic.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Match.MatcherApp.Basic

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

/-- The subterms of `e`, under its binders too (those mentioning a bound variable are of no use to a split). -/
private partial def inside (e : Expr) : List Expr :=
  e :: match e with
    | .app f a => inside f ++ inside a
    | .mdata _ b => inside b
    | .proj _ _ b => inside b
    | .lam _ t b _ => inside t ++ inside b
    | .forallE _ t b _ => inside t ++ inside b
    | .letE _ t v b _ => inside t ++ inside v ++ inside b
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

/-- One case split on the world's choices a `match` of the goal is on (owner §47): the first list of ticks (the time
the world lets pass, empty or a tick then the rest) or of faults or races (empty, or `true` or `false` then the
rest), in the goal (under its binders too) or a hypothesis. Only a match's: a list a world merely holds is no case of the run, so splitting
stops. -/
elab "frflow_choice_case" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let listNat ← mkAppM ``List #[mkConst ``Nat]
  let listBool ← mkAppM ``List #[mkConst ``Bool]
  let ofType (ty : Expr) (t : Expr) : MetaM Bool := do
    if t.hasLooseBVars || t.hasMVar || t.isAppOf ``List.cons || t.isAppOf ``List.nil then return false
    try isDefEq (← inferType t) ty catch _ => return false
  let hyps ← (← getLCtx).getFVarIds.toList.filterMapM (fun h => do
    let d ← h.getDecl
    if d.isImplementationDetail then return none else return some (← instantiateMVars d.type))
  let discriminants ← ((goal :: hyps).flatMap inside).filterMapM (fun e => do
    match ← Lean.Meta.matchMatcherApp? e with
    | some m => pure (some m.discrs.toList)
    | none => pure none)
  -- the innermost first: a variable, then a term holding no match of its own
  let plain ← discriminants.flatten.filterM (fun t => do
    return !(← (inside t).anyM (fun e => return (← Lean.Meta.matchMatcherApp? e).isSome)))
  let ds := plain.filter (·.isFVar) ++ plain.filter (!·.isFVar)
  if let some t ← ds.findM? (fun t => liftM (ofType listNat t)) then
    let s ← Term.exprToSyntax t
    if t.isFVar then evalTactic (← `(tactic| rcases $s:term with _ | ⟨_, ticks⟩))
    else evalTactic (← `(tactic| (generalize _hticks : $s = ticks at *; rcases ticks with _ | ⟨_, ticks⟩)))
  else if let some t ← ds.findM? (fun t => liftM (ofType listBool t)) then
    let s ← Term.exprToSyntax t
    if t.isFVar then evalTactic (← `(tactic| rcases $s:term with _ | ⟨_ | _, faults⟩))
    else evalTactic (← `(tactic| (generalize _hfaults : $s = faults at *; rcases faults with _ | ⟨_ | _, faults⟩)))
  else throwError "frflow_choice_case: no match on the world's choices to split on"
  for g in ← getGoals do
    if (← instantiateMVars (← g.getType)) == goal && (← g.getDecl).lctx.size == (← getLCtx).size then
      throwError "frflow_choice_case: the split made no progress"

/-- Every case of the faults a run takes, each computed. -/
macro "frflow_faults" : tactic => `(tactic| (intros; repeat (frflow_fault_case <;> try simp only [] at *)))

end FrFlow
