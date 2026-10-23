package frflow
package lean

/** Reading Lean: its output (`LeanOutput`, `Elaboration`), its source (`LeanSource`), and what a proof
  * file may hold (`ProofRules`), under one name.
  */
object Lean:
  export LeanOutput.{diagnostics, axioms, usesSorry}
  export LeanSource.{code, theorems, lemmaImports}
  export ProofRules.{allowedAxioms, forbidden, allowedCommands, violations, notAllowed, notAllowedInLemmas}
