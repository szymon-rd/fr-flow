package frflow.decision.review

import frflow.core.name.NodeId

/** Whether a decision is mechanical, one the developer takes in a batch (`confirm`), as today's rule in its order:
  * under review, holding no choice, only what follows from elsewhere moved, its meaning unmoved, new parts proven to
  * make it, proven again, and waiting for nothing the batch does not accept first.
  */
object Mechanical:
  enum Not:
    case HoldsAChoice
    case NotUnderReview(state: ReviewState)
    case CausesNeedTheDeveloper(causes: List[Cause])
    case MeaningMoved
    case PartsNotProven
    case NotProven(unproven: List[Unproven])
    case WaitsFor(id: NodeId)

  private val following: Set[Cause] = Set(Cause.Self, Cause.Above, Cause.Parts)

  /** Why `s` is not mechanical, or none; `others` holds the answer for the nodes it may wait for. */
  def why(r: Reading, s: Subject, others: Map[NodeId, Option[Not]]): Option[Not] =
    val causes = r.causes(s.id)
    Option.when(s.place.holdsChoice)(Not.HoldsAChoice)
      .orElse(Option.when(r.state(s.id) != ReviewState.Review)(Not.NotUnderReview(r.state(s.id))))
      .orElse(Option.when(!causes.forall(following))(Not.CausesNeedTheDeveloper(causes)))
      .orElse(Option.when(r.ledger.binding(s.id).forall(Meaning.decisionMoved(_, s)))(Not.MeaningMoved))
      .orElse(Option.when(causes.contains(Cause.Parts) && !s.proof.partsMake)(Not.PartsNotProven))
      .orElse(Option.unless(s.proof.provenAgain)(Not.NotProven(s.proof.unproven)))
      .orElse(r.waitsFor(s).filter(w => others.get(w).forall(_.isDefined)).map(Not.WaitsFor(_)))
