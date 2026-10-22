import Lean

/-!
`frflow_match_eqns`: generates, in the module that defines them, the equations of every `match`
the module declares (`f.match_1.eq_1`, its splitter, `f.match_1.congr_eq_1`, ...).

Lean otherwise generates them on first use, in the module that first needs them (`simp`, `grind`).
A `match` with overlapping patterns (`| .signIn t => .. | _ => ..`) gets, with them, an auxiliary
declaration named after them (`f.match_1.congr_eq_1._sparseCasesOn_2`). Two modules that each
generate them make that name twice, and a module importing both fails ("environment already
contains ..."). Generated here once, they are imported by every module that uses them: none makes
them again. Nothing is stated or proven by this command; it only fixes where Lean declares them.
-/

open Lean Elab Command Meta in
/-- Generates the equations of every `match` declared in this module (see the module doc). -/
elab "frflow_match_eqns" : command => do
  let env ← getEnv
  let ms := env.constants.map₂.foldl (fun acc n _ => if isMatcherCore env n then acc.push n else acc) #[]
  liftTermElabM do
    for m in ms do
      -- A match Lean cannot give equations for is left as it was: the proofs that need them say so.
      try discard <| Match.getEquationsFor m catch _ => pure ()
      try discard <| Match.genMatchCongrEqns m catch _ => pure ()
