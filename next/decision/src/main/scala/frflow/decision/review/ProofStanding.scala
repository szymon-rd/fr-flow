package frflow.decision.review

/** What the checks say of a node, as far as a mechanical decision needs: what is not proven again (today's
  * `Proofs.unproven`), and whether its parts are proven to make it with every try clean (today's `partsMake`).
  */
final case class ProofStanding(unproven: List[Unproven], partsMake: Boolean):
  /** Nothing open but that nothing below proves it, which a mechanical decision does not ask. */
  def provenAgain: Boolean = unproven.forall(_ == Unproven.NothingBelow)
