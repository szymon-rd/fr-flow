package frflow.decision.ledger

import frflow.core.name.NodeId

/** A ledger as it counts: only the decisions signed by a decider listed under their name whose signatures verify, of
  * nodes whose committed history is where their history now starts; and the others, each with why. The review states
  * are a fold of `counting` (`review.Standings`); the store keeps every decision, the others too.
  */
final case class Counted(counting: Ledger, others: List[(NodeId, Decision, Uncounted)])

object Counted:
  /** `committed`: the ledger as of the last commit, when one was read. */
  def of(working: Ledger, deciders: Option[Deciders], verify: Seals.Verifier, committed: Option[Ledger]): Counted =
    val judged = working.decisions.toList.sortBy(_._1).map((id, ds) =>
      id -> ds.map(d => d -> why(id, d, deciders, verify, rewritten(id, working, committed))))
    Counted(Ledger(judged.map((id, ds) => id -> ds.collect { case (d, None) => d }).filter(_._2.nonEmpty).toMap),
      judged.flatMap((id, ds) => ds.collect { case (d, Some(u)) => (id, d, u) }))

  /** The decisions `after` has that `counted` did not, added to `working`: what a decision taken on the ledger as
    * it counts stores.
    */
  def stored(working: Ledger, counted: Ledger, after: Ledger): Ledger =
    after.decisions.foldLeft(working)((l, kv) =>
      Ledger(l.decisions.updated(kv._1, l.history(kv._1) ++ kv._2.drop(counted.history(kv._1).size))))

  /** Whether the committed history of `id` is not where its history now starts. */
  private def rewritten(id: NodeId, working: Ledger, committed: Option[Ledger]): Boolean =
    committed.exists(c => !working.history(id).startsWith(c.history(id)))

  private def why(id: NodeId, d: Decision, ds: Option[Deciders], verify: Seals.Verifier, rewritten: Boolean)
      : Option[Uncounted] =
    if rewritten then Some(Uncounted.Rewritten)
    else ds.fold(Some(Uncounted.NoDeciders)) { list =>
      if !d.seal.exists(s => list.allows(d.author.by, s.key)) then Some(Uncounted.NotListed)
      else Option.unless(list.counts(verify)(id, d))(Uncounted.NotVerified)
    }
