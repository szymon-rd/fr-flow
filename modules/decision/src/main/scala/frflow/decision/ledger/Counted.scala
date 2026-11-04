package frflow.decision.ledger

import frflow.core.name.NodeId

/** A ledger as it counts: only the decisions signed by a decider listed under their name whose signatures verify, of
  * nodes whose history in each committed version of the ledger is where their history in the next version, and now,
  * starts; and the others, each with why (a node's history taken out entirely is reported by what was committed of
  * it). The review states are a fold of `counting` (`review.Standings`); the store keeps every decision, the others
  * too.
  */
final case class Counted(counting: Ledger, others: List[(NodeId, Decision, Uncounted)]):
  /** The nodes whose committed history was taken out or changed, or every node when a committed version does not
    * read: nothing may be decided until the ledger is restored.
    */
  def rewritten: List[NodeId] =
    others.collect { case (id, _, Uncounted.Rewritten | Uncounted.Unreadable) => id }.distinct

object Counted:
  /** `committed`: each committed version of the ledger, oldest first, none for one that does not read. */
  def of(working: Ledger, deciders: Option[Deciders], verify: Seals.Verifier, committed: List[Option[Ledger]])
      : Counted =
    if committed.exists(_.isEmpty) then
      Counted(Ledger.empty, all(working).map((id, d) => (id, d, Uncounted.Unreadable)))
    else
      val chain = committed.flatten :+ working
      val rewritten = chain.flatMap(_.decisions.keys).distinct.filter(id => broken(id, chain)).toSet
      val judged = all(working).map((id, d) => (id, d, if rewritten(id) then Some(Uncounted.Rewritten)
        else why(deciders, verify)(id, d)))
      val gone = rewritten.filterNot(working.decisions.contains).toList.sortBy(_.value).flatMap(id =>
        committed.flatten.reverse.find(_.history(id).nonEmpty).toList.flatMap(_.history(id))
          .map(d => (id, d, Uncounted.Rewritten)))
      Counted(Ledger(judged.collect { case (id, d, None) => id -> d }.groupMap(_._1)(_._2)),
        judged.collect { case (id, d, Some(u)) => (id, d, u) } ++ gone)

  /** The decisions `after` has that `counted` did not, added to `working`: what a decision taken on the ledger as
    * it counts stores.
    */
  def stored(working: Ledger, counted: Ledger, after: Ledger): Ledger =
    after.decisions.foldLeft(working)((l, kv) =>
      Ledger(l.decisions.updated(kv._1, l.history(kv._1) ++ kv._2.drop(counted.history(kv._1).size))))

  /** Every decision, nodes in the order of their ids, each node's oldest first. */
  private def all(l: Ledger): List[(NodeId, Decision)] =
    l.decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.map(id -> _))

  /** Whether a version holds of `id` a history the next one does not start with. */
  private def broken(id: NodeId, chain: List[Ledger]): Boolean =
    chain.zip(chain.drop(1)).exists((a, b) => !b.history(id).startsWith(a.history(id)))

  private def why(deciders: Option[Deciders], verify: Seals.Verifier)(id: NodeId, d: Decision): Option[Uncounted] =
    deciders.fold(Some(Uncounted.NoDeciders)) { list =>
      if !d.seal.exists(s => list.allows(d.author.by, s.key)) then Some(Uncounted.NotListed)
      else Option.unless(list.counts(verify)(id, d))(Uncounted.NotVerified)
    }
