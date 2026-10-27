package frflow.proof.obligation

/** One thing Lean is asked of a node: its name, its statement, how it is to be met, and the sentence the generated
  * Lean documents it with (made where the obligation is, from what it is about).
  */
final case class Obligation(name: ObligationName, goal: Prop, discharge: Discharge, doc: String)
