package frflow.decision.review

/** What the checks say of a node, as far as a mechanical decision needs: what is not proven again (today's
  * `Proofs.unproven`), whether its parts are proven to make it with every try clean (today's `partsMake`), and
  * whether Lean proves its code (an `Impl` or `RootImpl` obligation asked and proven; tested code is not).
  */
final case class ProofStanding(unproven: List[Unproven], partsMake: Boolean, codeProven: Boolean):
  /** Nothing open but that nothing below proves it, which a mechanical decision does not ask. */
  def provenAgain: Boolean = unproven.forall(_ == Unproven.NothingBelow)
