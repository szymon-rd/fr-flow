package frflow.project.check

import frflow.proof.reading.Elaboration

/** The developer's proofs of the theory's own obligations as Lean read them: whether the file holds only what a proof
  * file may, what Lean said of it, and the audit of what each proof rests on.
  */
final case class Authored(allowed: Boolean, proof: Option[Elaboration], audit: Option[Elaboration])
