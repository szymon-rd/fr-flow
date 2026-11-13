package frflow.proof.obligation

/** One thing Rocq is asked of a node: its name, its statement, how it is to be met, and the sentence the generated
  * module documents it with (made where the obligation is, from what it is about).
  */
final case class Obligation(name: ObligationName, goal: Prop, discharge: Discharge, doc: String)
