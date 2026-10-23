package frflow
package ledger

import frflow.protocol.*
import io.circe.Json
import ReviewState.{Accepted, Proposed, Rejected}

/** The shape of a snapshot, apart from any decision: what rests on what, the order of decisions, the alternatives, the chains. */
final class Graph(val snapshot: Snapshot):
  val nodes: List[SnapNode] = snapshot.nodes
  val byId: Map[NodeId, SnapNode] = nodes.map(n => n.id -> n).toMap
  val children: Map[NodeId, List[SnapNode]] = nodes.flatMap(n => n.parents.map(_ -> n)).groupMap(_._1)(_._2)
  val dependents: Map[NodeId, List[SnapNode]] =
    nodes.flatMap(n => (n.parents ++ n.uses ++ n.relies ++ n.invariants.map(_.id)).distinct.map(_ -> n)).groupMap(_._1)(_._2)
  def dependentsOf(id: NodeId): List[SnapNode] = dependents.getOrElse(id, Nil)
  def restsOn(n: SnapNode): List[NodeId] = (n.parents ++ n.uses ++ n.relies).distinct.filter(byId.contains)
  /** Every node after all it rests on: the order decisions are taken in, a batch's too. */
  lazy val order: List[NodeId] = Walk.postorder(nodes.map(_.id), identity)(id => byId.get(id).fold(Nil)(restsOn))
  lazy val rank: Map[NodeId, Int] = order.zipWithIndex.toMap
  /** Everything `n` rests on, however far up, nearest first. */
  def ancestry(n: SnapNode): List[NodeId] = Walk.breadthFirst(restsOn(n), identity)(id => byId.get(id).fold(Nil)(restsOn))
  /** Through its parents only, each once. */
  def ancestors(n: SnapNode): List[SnapNode] =
    Walk.preorder(n.parents, identity)(id => byId.get(id).fold(Nil)(_.parents)).flatMap(byId.get)
  lazy val rivals: Map[NodeId, List[NodeId]] =
    val byTerm = nodes.flatMap(n => n.defines.map(_ -> n)).groupMap(_._1)(_._2)
    val replacing = nodes.flatMap(n => n.replaces.flatMap(byId.get).toList.flatMap(r => List(n -> r, r -> n)))
    (replacing ++ nodes.flatMap(n => n.defines.flatMap(byTerm.getOrElse(_, Nil)).map(n -> _)))
      .filter((a, b) => a.id != b.id && Graph.alternatives(a, b))
      .groupMap(_._1.id)(_._2.id).view.mapValues(_.distinct.sortBy(x => rank.getOrElse(x, 0))).toMap
  private lazy val chains: Map[NodeId, Chain] = chainsOver(order)

  /** What a node rests on, as decided; a design decision rests on its parents' place, not their meaning. */
  def parentChain(n: SnapNode): Chain = parentChainFrom(n, chains)

  private def chainsOver(ids: List[NodeId]): Map[NodeId, Chain] =
    ids.flatMap(byId.get).foldLeft(Map.empty[NodeId, Chain])((done, n) =>
      done.updated(n.id, Meaning.chain(n.content, parentChainFrom(n, done))))

  private def parentChainFrom(n: SnapNode, chains: Map[NodeId, Chain]): Chain =
    if n.kind == NodeKind.Design then Chain.empty
    else Meaning.above(Chain.empty, restsOn(n).map(chains.getOrElse(_, Chain.empty)))

object Graph:
  /** One replaces the other, or both define one term. Parts under one parent are not: together they make it. */
  def alternatives(a: SnapNode, b: SnapNode): Boolean =
    a.replaces.contains(b.id) || b.replaces.contains(a.id) || a.defines.intersect(b.defines).nonEmpty

/** A snapshot read with a ledger: each node's standing, wait and mechanical answer computed once, parents first. */
final class Reading(val graph: Graph, val ledger: Ledger):
  def snapshot: Snapshot = graph.snapshot
  lazy val standings: Map[NodeId, Standing] = Standing.all(graph, ledger)
  def standing(n: SnapNode): Standing = standings.getOrElse(n.id, Standing.of(graph, ledger, standings, n))
  def state(n: SnapNode): ReviewState = standing(n).state
  def causes(n: SnapNode): List[Cause] = standing(n).causes
  /** A node not in the model is not decided. */
  def stateOf(id: NodeId): ReviewState = graph.byId.get(id).fold(Proposed)(state)
  def holds(id: NodeId): Boolean = stateOf(id) == Accepted
  /** Where the developer stands on IDEA.md; the root is decided after it. */
  lazy val idea: Option[IdeaReview] = IdeaDecision.review(snapshot, ledger)

  /** What the developer saw of a node: a decision sent with it is refused if the node moved since. */
  def version(n: SnapNode): Version =
    Version(Sha.parts(n.hash.value, graph.parentChain(n).value, n.code.fold("")(_.fingerprint.value)).take(16))

  /** A parent not chosen; or, when `n` rests on its parents (proposed, or they moved), what it rests on not accepted. */
  def waitsFor(n: SnapNode): Option[NodeId] =
    val restsOnParent = state(n) == Proposed || causes(n).contains(Cause.Above)
    n.parents.find(p => graph.byId.get(p).map(state).exists(s => s == Proposed || s == Rejected || (restsOnParent && s != Accepted)))
      .orElse(Option.when(restsOnParent)((n.uses ++ n.relies).find(i => graph.byId.get(i).exists(x => state(x) != Accepted))).flatten)
      .orElse(Option.when(snapshot.root.contains(n.id) && idea.exists(_.state != Accepted))(IdeaDecision.Id))

  /** Why each node is not mechanical, or None if it is, parents first. */
  lazy val notMechanical: Map[NodeId, Option[String]] =
    graph.order.flatMap(graph.byId.get).foldLeft(Map.empty[NodeId, Option[String]])((done, n) =>
      done.updated(n.id, Mechanical.why(this, n, done)))
  def mechanical(n: SnapNode): Option[String] = Mechanical.why(this, n, notMechanical)
  /** The mechanical decisions, in the order they are taken: the batch `confirm` accepts. */
  def mechanicalBatch: List[NodeId] = graph.order.filter(id => notMechanical.get(id).exists(_.isEmpty))

object Reading:
  def apply(snapshot: Snapshot, ledger: Ledger): Reading = new Reading(Graph(snapshot), ledger)
  def apply(graph: Graph, ledger: Ledger): Reading = new Reading(graph, ledger)

/** Where the developer stands on a node. A decision binds a reason to the hash of what was seen: whatever moves
  * under it puts the node back up for review, with its causes.
  */
final case class Standing(state: ReviewState, causes: List[Cause])

object Standing:
  def all(g: Graph, ledger: Ledger): Map[NodeId, Standing] =
    g.order.flatMap(g.byId.get).foldLeft(Map.empty[NodeId, Standing])((done, n) => done.updated(n.id, of(g, ledger, done, n)))

  def of(g: Graph, ledger: Ledger, done: Map[NodeId, Standing], n: SnapNode): Standing =
    // A parent rejected moves it as a change of its parent's meaning would: what it rests on is no longer chosen.
    val parentRejected = n.parents.exists(p => done.get(p).exists(_.state == Rejected))
    val causes = ledger.binding(n.id).fold(Nil) { d =>
      val moved = d.hash != n.hash
      List(
        Cause.Self -> (moved && Meaning.own(d.content).hash != Meaning.own(n.content).hash),
        Cause.Above -> ((d.chain != g.parentChain(n) && !reworded(g, ledger, n, d)) || parentRejected),
        // A part added or removed, in any order.
        Cause.Parts -> (moved && d.content.parts.exists(_.toSet != n.content.parts.getOrElse(Nil).toSet)),
        Cause.Code -> (d.code != n.code.map(_.fingerprint)),
        Cause.Revisit -> ledger.current(n.id).exists(_.action == Action.Revisit),
        Cause.Merged -> ledger.forked(n.id)
      ).collect { case (c, true) => c }
    }
    val state = ledger.current(n.id) match
      case Some(d) if d.action == Action.Reject => if d.hash == n.hash then Rejected else Proposed
      case Some(d) if d.action.binds || d.action == Action.Revisit => if causes.nonEmpty then ReviewState.Review else Accepted
      case _ => Proposed
    Standing(state, causes)

  /** With each formal node above `n` whose Lean did not change taken as decided when `d` was, the chain is `d`'s again:
    * rewording a formal node reviews it only, the decisions below listed under it (`below`), not sent to review.
    */
  private def reworded(g: Graph, ledger: Ledger, n: SnapNode, d: Decision): Boolean =
    val rests = g.ancestry(n).toSet
    val was: Map[NodeId, Hash] = rests.toList.flatMap(a => g.byId.get(a).toList.flatMap { now =>
      ledger.history(a).filter(x => x.action.binds && !x.at.isAfter(d.at)).lastOption.map(_.content)
        .filter(c => Meaning.hasFormal(now.content) && Meaning.of(c) != Meaning.of(now.content) &&
          Meaning.formal(c) == Meaning.formal(now.content))
        .map(c => a -> Meaning.of(c))
    }).toMap
    def touched(x: SnapNode, touchedAbove: Set[NodeId]) = g.restsOn(x).exists(a => was.contains(a) || touchedAbove(a))
    // As `Graph.parentChain`, with the reworded nodes as decided; a design node keeps its own.
    def restOf(x: SnapNode, isTouched: Boolean, chains: Map[NodeId, Chain]) =
      if !isTouched || x.kind == NodeKind.Design then g.parentChain(x)
      else Meaning.above(Chain.empty, g.restsOn(x).map(chains.getOrElse(_, Chain.empty)))
    was.nonEmpty && {
      val (touchedAbove, chains) = g.order.filter(rests).flatMap(g.byId.get)
        .foldLeft((Set.empty[NodeId], Map.empty[NodeId, Chain])) { case ((t, cs), x) =>
          val isTouched = touched(x, t)
          (if isTouched then t + x.id else t,
            cs.updated(x.id, Meaning.chainOf(was.getOrElse(x.id, Meaning.of(x.content)), restOf(x, isTouched, cs))))
        }
      restOf(n, touched(n, touchedAbove), chains) == d.chain
    }

/** Whether a decision is mechanical, one the developer takes in a batch: under review, holding no choice Lean does not
  * check, only what follows from elsewhere changed, proven again (new parts proven to make it, their tries clean).
  */
object Mechanical:
  /** Why `n` is not mechanical, or None if it is; `others` holds the answer for what it waits for. */
  def why(v: Reading, n: SnapNode, others: Map[NodeId, Option[String]]): Option[String] =
    val id = n.id
    val cs = v.causes(n)
    val (ok, total) = n.examplesPassing
    // The new parts are decided on their own; `needed` not shown says only that Lean found no proof without one.
    def partsMake = n.split.exists(sp => sp.complete.status == ObligationStatus.Proven &&
      sp.needed.forall(_.status == ObligationStatus.NotShown) && sp.clash.status != ObligationStatus.Shown)
    Option.when(n.kind == NodeKind.Design || n.kind == NodeKind.Definition)(s"${n.kind} nodes hold a choice")
      .orElse(Option.when(v.state(n) != ReviewState.Review)(s"$id is ${v.state(n)}: only a node under review can be mechanical"))
      .orElse(Option.when(cs.exists(c => !Set(Cause.Self, Cause.Above, Cause.Parts)(c)))(
        s"$id is under review for ${cs.mkString(", ")}: the developer decides"))
      .orElse(Option.when(v.ledger.binding(id).forall(Meaning.decisionMoved(_, n)))(s"what $id says changed: the developer decides"))
      .orElse(Option.when(cs.contains(Cause.Parts) && !partsMake)(
        s"$id's parts changed and Lean does not prove they make it, or shows one not needed or a clash: the developer decides"))
      .orElse(Option.when(!Proofs.unproven(n).forall(_.startsWith("nothing below proves it")))(
        s"$id is not proven: only what Lean proves again is mechanical"))
      .orElse(Option.when(ok != total)(s"${total - ok} of $id's examples fail"))
      .orElse(Option.when(n.invariants.exists(i => i.status != ObligationStatus.Proven && i.status != ObligationStatus.Exempt))(
        s"an invariant $id keeps is not proven"))
      // Waiting for a node that is itself mechanical is no wait: the batch accepts it first.
      .orElse(v.waitsFor(n).filter(w => v.graph.byId.get(w).forall(_ => others.get(w).forall(_.isDefined))).map(w => s"$id waits for $w"))

/** What a node's content means, apart from its wording: what a decision is bound to, and what moves the decisions below. */
object Meaning:
  /** Its content without parts, parents and `.under(...)` calls (its causes `parts` and `above`); a design keeps its place. */
  def own(c: Content): Content =
    if c.isDesign then c.without(_ == "parts")
    else Content(c.fields.flatMap {
      case ("parts" | "parents", _) => None
      case ("definition", j) => Some("definition" -> j.asString.fold(j)(src => Json.fromString(src.replaceAll("""\s*\.under\([^()]*\)""", ""))))
      case f => Some(f)
    }*)

  def above(parentChain: Chain, otherChains: List[Chain]): Chain =
    if otherChains.isEmpty then parentChain else Chain(Sha.parts((parentChain :: otherChains.sorted).map(_.value)*))

  /** Its meaning with what it rests on: rewording its reason, adding an example or editing the idea reviews only the node. */
  def chain(content: Content, parentChain: Chain): Chain = chainOf(of(content), parentChain)
  def chainOf(meaning: Hash, parentChain: Chain): Chain = Chain(Sha.parts(meaning.value, parentChain.value))

  private val meaningful = Set("statement", "sources", "substitutions", "vocabulary", "uses", "governs", "op")

  /** Without its reason, examples, idea or parents' names (the chain holds their meaning): renaming reviews nothing below. */
  def of(content: Content): Hash = content.only(meaningful).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  def formal(content: Content): Hash = of(content.without(_ == "statement"))

  /** A formula, a post, a rule, or a definition's terms: what Lean reads of a node. */
  def hasFormal(c: Content): Boolean =
    c("sources").exists(_.asObject.exists(_.nonEmpty)) || c("substitutions").exists(_.asArray.exists(_.nonEmpty))

  private val DefinitionUse = """(?s)^[A-Za-z_]\w* = .*""".r

  /** Apart from what follows from elsewhere: the types it uses, how its examples print, a proven implementation. */
  def decisionMoved(d: Decision, n: SnapNode): Boolean =
    val proven = n.implementationProof.exists(_.status == ObligationStatus.Proven)
    def decided(content: Content) =
      val c = own(content)
      // A definition it calls (`name = body`) is part of what it says.
      val definitions = c("uses").flatMap(_.asArray).fold(Vector.empty[Json])(_.filter(_.asString.exists(DefinitionUse.matches)))
      val examples = c.strs("examples").map(e => Json.fromString(e.takeWhile(_ != ' ') + " — " + e.split(" — ").lastOption.getOrElse("")))
      (c.without(k => k == "uses" || k == "examples" || (proven && k == "implementation")) :+
        ("definitions" -> Json.fromValues(definitions)) :+ ("examples" -> Json.fromValues(examples))).hash
    decided(d.content) != decided(n.content)
