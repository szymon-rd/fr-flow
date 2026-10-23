package frflow.api

import cats.syntax.all.*
import frflow.ledger.Decisions
import frflow.protocol.*

/** A front end's decision as the ledger's decisions: pure, the same for a preview and for the record.
  * Several nodes are decided in the order decisions are taken (each after what it rests on), all or none.
  */
object Deciding:
  /** Where the decision is taken: when, and the code checked out then (see `Decision.commit`, `tree`). */
  final case class At(time: String, commit: Option[String] = None, tree: Option[String] = None)

  def apply(v: View, ledger: Ledger, d: Decide, by: Developer, at: At): Either[Refusal, Ledger] =
    val s = v.snapshot
    def run(l: Ledger, r: DecisionRequest) =
      Decisions.decide(s, l, r, at.time, at.commit, at.tree).leftMap(why => Refusal(s"${r.node}: $why"))
    def each(ids: List[NodeId])(request: (Ledger, NodeId) => DecisionRequest) =
      ids.foldLeftM(ledger)((l, id) => run(l, request(l, id)))
    def plain(id: NodeId, reason: String, seen: Option[String] = None, action: Action = Action.Accept) =
      DecisionRequest(id, by.name, reason, action = action, seen = seen)
    d match
      case Decide.Accept(nodes, reason, revisit, seen) =>
        val unknown = nodes.filter(id => v.node(id).isEmpty && !v.annotated.gone.exists(_.id == id))
        if nodes.isEmpty then Left(Refusal("name the nodes to accept"))
        else if unknown.nonEmpty then Left(Refusal(s"unknown node ${unknown.mkString(", ")}"))
        else notBelow(v, ledger, nodes, revisit) *>
          each(inOrder(v, nodes))((l, id) => accept(v, l, id, by, reason, revisit, seen.get(id)))
      case Decide.Reject(node, reason, seen) => run(ledger, plain(node, reason, seen, Action.Reject))
      case Decide.Confirm(reason) =>
        val batch = Queue.mechanical(v)
        if batch.isEmpty then Left(Refusal("no mechanical decision waits"))
        else each(batch.map(_.id))((_, id) => plain(id, reason, v.node(id).map(_.review.version)))
      case Decide.Revisit(node, reason) => revisit(v, ledger, node, reason, by, at)
      case Decide.Gone(node, reason) =>
        if !v.annotated.gone.exists(_.id == node) then Left(Refusal(s"$node is not gone from the model"))
        else run(ledger, plain(node, reason))

  /** Each after what it rests on (`Decisions.order`). */
  private def inOrder(v: View, ids: List[NodeId]): List[NodeId] =
    val rank = Decisions.order(v.snapshot).zipWithIndex.toMap
    ids.distinct.sortBy(id => rank.getOrElse(id, Int.MaxValue))

  /** Accepting a node rejects its rivals not rejected yet; of the decisions below it, those named are
    * revisited, and those under review only because it moved are confirmed. A gone node is agreed gone.
    */
  private def accept(v: View, l: Ledger, id: NodeId, by: Developer, reason: String, revisit: List[NodeId],
      seen: Option[String]): DecisionRequest =
    val s = v.snapshot
    v.node(id).fold(DecisionRequest(id, by.name, reason)) { r =>
      val rivals = r.review.rivals.filter(x => v.node(x).exists(o => Decisions.state(s, l, o.node) != ReviewState.Rejected))
      val below = Decisions.below(s, l, r.node)
      DecisionRequest(id, by.name, reason, reject = rivals, revisit = revisit.filter(x => below.exists(_.id == x)),
        confirm = below.filter(_.kind == BelowKind.Moved).map(_.id).filterNot(revisit.contains), seen = seen)
    }

  private def notBelow(v: View, l: Ledger, nodes: List[NodeId], revisit: List[NodeId]): Either[Refusal, Unit] =
    val below = nodes.flatMap(v.node).flatMap(r => Decisions.below(v.snapshot, l, r.node)).map(_.id).toSet
    revisit.filterNot(below) match
      case Nil => Right(())
      case xs => Left(Refusal(s"not among the decisions below ${nodes.mkString(", ")} that this decision can act on: ${xs.mkString(", ")}"))

  /** A reason says something: a few words, not a placeholder. */
  private def tooFew(reason: String): Boolean = reason.trim.split("\\s+").count(_.exists(_.isLetter)) < 3

  /** The developer asks that an accepted node be reviewed again. (The ledger's `decide` takes accept and
    * reject only; this is the decision it records for a revisit below a change, asked of one node.)
    */
  private def revisit(v: View, l: Ledger, id: NodeId, reason: String, by: Developer, at: At): Either[Refusal, Ledger] =
    v.node(id) match
      case None => Left(Refusal(s"unknown node $id"))
      case Some(_) if tooFew(reason) => Left(Refusal("give the reason in a few words: it is kept as part of the theory"))
      case Some(r) if l.binding(id).isEmpty => Left(Refusal(s"$id is ${r.state}: only a decided node is revisited"))
      case Some(_) if l.current(id).exists(_.action == Action.Revisit) => Left(Refusal(s"$id is already to revisit"))
      case Some(r) =>
        Right(l.add(id, Decision(Action.Revisit, by.name, at.time, reason, code = r.node.code.map(_.fingerprint),
          commit = at.commit, tree = at.tree, chain = Decisions.parentChain(v.snapshot, r.node), content = r.node.content)))

  /** The decisions `after` has that `before` did not, in the order they are taken. */
  def added(v: View, before: Ledger, after: Ledger): Decided =
    Decided(inOrder(v, after.decisions.keys.toList.sorted).flatMap(id => after.history(id).drop(before.history(id).size).map(Logged(id, _))))
