package frflow
package ledger

import frflow.protocol.*
import io.circe.Json
import scala.collection.mutable

/** The developer's position on each node, computed from the snapshot and the ledger, and the one
  * way to record a decision. Shared by every command.
  *
  * The rule: a decision binds a person's reason to the hash of what they saw. Whatever moves
  * under it puts the node back up for review.
  *
  * A snapshot node carries `content` (what the developer sees and decides), its `hash`, its edges and,
  * if it governs code, a `code` fingerprint. Its chain (the meaning of what it rests on) is computed
  * here, from the edges.
  *
  * States:
  *   - `proposed`: not decided yet (or rejected, then reworked);
  *   - `accepted`: decided by the developer, and nothing moved since;
  *   - `review`: something moved since it was decided; `causes` say what:
  *     `self` (what the node itself says changed), `above` (the meaning of what it rests on changed:
  *     any of its parents, of the definitions it uses, of the contracts its code calls, however far
  *     up; one cause however many paths lead there), `parts` (a part was added or removed: its parts
  *     are decided with it), `code` (the code it governs changed), `revisit` (the
  *     developer said a change above, such as an edit of the idea, may affect it), `merged` (two
  *     branches decided it, and a merge kept both); a decided node no longer in the model is listed
  *     under `gone`;
  *   - `rejected`: an alternative was chosen instead; the agent removes it from the model.
  *
  * The developer accepts or rejects (see `Request`). Accepting a proposal chooses it (rejecting
  * alternatives); accepting a node under review says it holds as it now is (recorded as a
  * confirmation when only something above it or its code moved, so the reason it was chosen
  * stays); accepting a gone node agrees that it is gone. Accepting a change, the developer goes
  * through the decisions below with their reasons, where the conditions for revisiting them are
  * written: each is revisited or confirmed, by name.
  */
object Decisions:
  import ReviewState.{Accepted, Proposed, Rejected}

  /** The snapshot and ledger, with each node's chain, state and causes computed once. */
  private final class View(val snapshot: Snapshot, val ledger: Ledger):
    val all: List[SnapNode] = snapshot.nodes
    val ids: Map[NodeId, SnapNode] = all.map(n => n.id -> n).toMap
    val children: Map[NodeId, List[SnapNode]] = all.flatMap(n => n.parents.map(_ -> n)).groupMap(_._1)(_._2)
    /** What rests on each node: its parts, the nodes that use it (a definition), the nodes whose code
      * calls it (a contract), and the contracts that keep it (an invariant). A change of its meaning
      * shows on each, as `above`.
      */
    val dependents: Map[NodeId, List[SnapNode]] =
      all.flatMap(n => (n.parents ++ n.uses ++ n.relies ++ n.invariants.map(_.id)).distinct.map(_ -> n)).groupMap(_._1)(_._2)
    /** What a node rests on: its parents, the definitions it uses, the contracts its code calls. */
    def restsOn(n: SnapNode): List[NodeId] = (n.parents ++ n.uses ++ n.relies).distinct.filter(ids.contains)
    /** Every node after all it rests on (see `Decisions.order`). */
    lazy val order: List[NodeId] =
      val done = mutable.LinkedHashSet.empty[NodeId]
      def visit(id: NodeId, seen: Set[NodeId]): Unit =
        if !done(id) && !seen(id) then
          ids.get(id).foreach(n => restsOn(n).foreach(visit(_, seen + id)))
          done += id
      all.foreach(n => visit(n.id, Set.empty))
      done.toList
    lazy val rank: Map[NodeId, Int] = order.zipWithIndex.toMap
    /** The nodes of the model that are alternatives to each (see `alternatives`). */
    lazy val rivals: Map[NodeId, List[NodeId]] =
      val byTerm = all.flatMap(n => n.defines.map(_ -> n)).groupMap(_._1)(_._2)
      val replacing = all.flatMap(n => n.replaces.flatMap(ids.get).toList.flatMap(r => List(n -> r, r -> n)))
      (replacing ++ all.flatMap(n => n.defines.flatMap(byTerm.getOrElse(_, Nil)).map(n -> _)))
        .filter((a, b) => a.id != b.id && alternatives(a, b))
        .groupMap(_._1.id)(_._2.id).view.mapValues(_.distinct.sortBy(x => rank.getOrElse(x, 0))).toMap
    private val chains = mutable.Map.empty[NodeId, Chain]
    private val states = mutable.Map.empty[NodeId, ReviewState]
    private val causeMemo = mutable.Map.empty[NodeId, List[Cause]]
    /** A node's chain: its meaning, with what it rests on. */
    def chainOf(id: NodeId): Chain = chains.getOrElseUpdate(id, ids.get(id).fold(Chain.empty)(n => chain(n.content, parentChain(n))))
    /** What a node rests on: the chains of its parents, of the definitions it uses and of the contracts
      * its code calls. A design decision rests on its parents' place, not their meaning: a change above
      * lists it below, to revisit.
      */
    def parentChain(n: SnapNode): Chain =
      if n.kind == NodeKind.Design then Chain.empty else above(Chain.empty, restsOn(n).map(chainOf))
    def causes(n: SnapNode): List[Cause] = causeMemo.getOrElseUpdate(n.id, {
      val revisit = ledger.current(n.id).exists(_.action == Action.Revisit)
      val parentRejected = n.parents.flatMap(ids.get).exists(p => state(p) == Rejected)
      ledger.binding(n.id).fold(Nil) { d =>
        val moved = d.hash != n.hash
        List(Cause.Self -> (moved && selfChanged(d, n)), Cause.Above -> ((d.chain != parentChain(n) && !reworded(n, d)) || parentRejected),
          Cause.Parts -> (moved && partsChanged(d, n)), Cause.Code -> (d.code != n.code.map(_.fingerprint)),
          Cause.Revisit -> revisit, Cause.Merged -> ledger.forked(n.id)).collect { case (c, true) => c }
      }
    })
    /** Whether what `n` rests on moved only in its words: with each formal node above it whose Lean did
      * not change (its statement reworded) taken as it was decided when `d` was, the chain is `d`'s again.
      * Rewording a formal node reviews that node only; the decisions below it are listed under it (`below`),
      * not sent to review. A node out of Lean (`formal = false`) is its words: rewording it moves what is below.
      */
    private def reworded(n: SnapNode, d: Decision): Boolean =
      val rests = mutable.LinkedHashSet.empty[NodeId]
      def up(x: SnapNode): Unit = restsOn(x).foreach(a => if rests.add(a) then ids.get(a).foreach(up))
      up(n)
      val was: Map[NodeId, Hash] = rests.toList.flatMap(a => ids.get(a).toList.flatMap { now =>
        ledger.history(a).filter(x => x.action.binds && x.at <= d.at).lastOption.map(_.content)
          .filter(c => formalNode(now.content) && meaning(c) != meaning(now.content) && formalMeaning(c) == formalMeaning(now.content))
          .map(c => a -> meaning(c))
      }).toMap
      was.nonEmpty && {
        val reaches = mutable.Map.empty[NodeId, Boolean]
        def touched(x: SnapNode): Boolean = reaches.getOrElseUpdate(x.id, restsOn(x).exists(a => was.contains(a) || ids.get(a).exists(touched)))
        val chains = mutable.Map.empty[NodeId, Chain]
        def chainOf(a: NodeId): Chain = chains.getOrElseUpdate(a, ids.get(a).fold(Chain.empty)(x => chainOfMeaning(was.getOrElse(a, meaning(x.content)), restOf(x))))
        // As `parentChain`: a design node keeps its own.
        def restOf(x: SnapNode): Chain =
          if !touched(x) || x.kind == NodeKind.Design then parentChain(x)
          else above(Chain.empty, restsOn(x).map(chainOf))
        restOf(n) == d.chain
      }
    def state(n: SnapNode): ReviewState = states.getOrElseUpdate(n.id,
      ledger.current(n.id) match
        case Some(d) if d.action == Action.Reject => if d.hash == n.hash then Rejected else Proposed
        case Some(d) if d.action.binds || d.action == Action.Revisit =>
          if causes(n).nonEmpty then ReviewState.Review else Accepted
        case _ => Proposed)

  private var last: View = View(Snapshot("", Nil), Ledger.empty)
  /** What does not depend on the ledger: the last view, if it is of this snapshot. */
  private def structure(snapshot: Snapshot): View = synchronized { if last.snapshot eq snapshot then last else view(snapshot, last.ledger) }
  private def view(snapshot: Snapshot, ledger: Ledger): View = synchronized {
    if !(last.snapshot eq snapshot) || !(last.ledger eq ledger) then last = View(snapshot, ledger)
    last
  }
  private def byId(snapshot: Snapshot): Map[NodeId, SnapNode] = structure(snapshot).ids

  /** What a node says itself: its content without its edges. Its parts are decided with it, but under
    * their own cause (`parts`); its parents are what it rests on (`above`), and the calls that place it
    * under them (`.under(...)`) are left out of the source it is written in. A design decision rests on
    * its parents' place, not their meaning: for it, where it is is what it says.
    */
  private def ownContent(c: Content): Content =
    if c.isDesign then c.without(_ == "parts")
    else Content(c.fields.flatMap {
      case ("parts" | "parents", _) => None
      case ("definition", j) => Some("definition" -> j.asString.fold(j)(src => Json.fromString(withoutEdges(src))))
      case f => Some(f)
    }*)
  private def withoutEdges(src: String): String = src.replaceAll("""\s*\.under\([^()]*\)""", "")

  /** Whether what the node says itself changed since it was decided (see `ownContent`). */
  private def selfChanged(d: Decision, n: SnapNode): Boolean = ownContent(d.content).hash != ownContent(n.content).hash

  /** Whether a part was added or removed since the node was decided (in any order). */
  private def partsChanged(d: Decision, n: SnapNode): Boolean =
    d.content.parts.exists(_.toSet != n.content.parts.getOrElse(Nil).toSet)

  /** The node holds as decided. */
  private def holds(state: ReviewState): Boolean = state == Accepted

  /** What a node rests on: its parents' chain with the chains of the definitions it uses and the
    * contracts its code calls.
    */
  def above(parentChain: Chain, otherChains: List[Chain]): Chain =
    if otherChains.isEmpty then parentChain else Chain(Sha.parts((parentChain :: otherChains.sorted).map(_.value)*))

  /** A reason says something: a few words, not a placeholder (as `Words.tooFew` of the model). */
  private def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3

  /** A node's chain: what its content means, together with what it rests on. A change to a node's
    * meaning puts the nodes below up for review; rewording its reason, adding an example, or editing
    * the idea reviews only the node itself.
    */
  def chain(content: Content, parentChain: Chain): Chain = chainOfMeaning(meaning(content), parentChain)
  private def chainOfMeaning(meaning: Hash, parentChain: Chain): Chain = Chain(Sha.parts(meaning.value, parentChain.value))

  /** What a node's content means, without its reason, examples or idea; and without its parent's
    * name (the chain holds the parent's meaning), so renaming a node reviews nothing below it.
    */
  def meaning(content: Content): Hash =
    val parts = Set("statement", "sources", "substitutions", "vocabulary", "uses", "governs", "formal", "op")
    content.only(parts).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  private def formalMeaning(content: Content): Hash = meaning(content.without(_ == "statement"))

  /** A formula, a post, a rule, or a definition's terms: what Lean reads of a node. */
  private def hasFormal(c: Content): Boolean =
    c("sources").exists(_.asObject.exists(_.nonEmpty)) || c("substitutions").exists(_.asArray.exists(_.nonEmpty))

  /** A node Lean reads, not out of Lean (`formal = false`). */
  private def formalNode(content: Content): Boolean = !content("formal").contains(Json.False) && hasFormal(content)

  /** The `## ` sections of the idea (without Not modelled), by heading, after the text before the
    * first one (which every section-root is also decided against).
    */
  def ideaSections(decided: String): (String, List[(String, String)]) =
    val lines = decided.linesIterator.toList
    val (intro, rest) = lines.span(l => !l.startsWith("## "))
    def go(ls: List[String]): List[(String, String)] = ls match
      case h :: tail =>
        val (body, more) = tail.span(l => !l.startsWith("## "))
        (h.stripPrefix("## ").trim -> (h :: body).mkString("\n").trim) :: go(more)
      case Nil => Nil
    (intro.mkString("\n").trim, go(rest))

  /** IDEA.md split into the idea a root is decided against, and its `## Not modelled` section. */
  def splitIdea(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    val i = lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled"))
    if i < 0 then (idea.trim, "")
    else
      val (section, rest) = lines.drop(i + 1).span(l => !(l.startsWith("# ") || l.startsWith("## ")))
      ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)

  /** What a node rests on, as decided (see `View.parentChain`). */
  def parentChain(snapshot: Snapshot, n: SnapNode): Chain = structure(snapshot).parentChain(n)

  /** What moved under a node's decision. A node whose parent was rejected is reviewed as if its
    * parent's meaning moved: what it rests on is no longer chosen.
    */
  def causes(snapshot: Snapshot, ledger: Ledger, n: SnapNode): List[Cause] = view(snapshot, ledger).causes(n)

  def state(snapshot: Snapshot, ledger: Ledger, n: SnapNode): ReviewState = view(snapshot, ledger).state(n)

  /** What the developer saw of a node: a decision sent with it is refused if the node moved since. */
  def version(snapshot: Snapshot, n: SnapNode): String =
    Sha.parts(n.hash.value, parentChain(snapshot, n).value, n.code.fold("")(_.fingerprint.value)).take(16)

  /** The snapshot with each node's state, what moved, its decision, history and alternatives;
    * and the decided nodes that are gone from the model.
    */
  def annotate(snapshot: Snapshot, ledger: Ledger): Annotated =
    val v = view(snapshot, ledger)
    def sources(n: SnapNode) = n.content("sources").flatMap(_.asObject).filter(_.nonEmpty).map(o => Content.of(o).hash)
    val nodes = snapshot.nodes.map { n =>
      val id = n.id
      val st = v.state(n)
      Reviewed(n, Review(
        state = st,
        causes = v.causes(n),
        version = version(snapshot, n),
        waitsFor = waitsFor(snapshot, ledger, n),
        moved = moved(snapshot, ledger, n),
        decision = ledger.chosen(id),
        reasonNow = ledger.binding(id).map(_ => reasonNow(ledger, id)),
        notMechanical = mechanical(snapshot, ledger, n),
        resembles = resembles(ledger, n),
        unproven = Reports.unproven(n),
        // A sibling that says formally the same: the statement may claim more than the spec.
        sameAs = n.parents.flatMap(p => v.children.getOrElse(p, Nil)).distinctBy(_.id)
          .filter(m => m.id != id && m.kind == n.kind && sources(m).isDefined && sources(m) == sources(n)).map(_.id),
        rejectedBeside = n.parents.flatMap(ledger.rejectedUnder).distinctBy(_._1).filter(_._1 != id)
          .map((r, c, why) => RejectedBeside(r, c.statement, c.why, why)),
        below = if st == Accepted then Nil else below(snapshot, ledger, n),
        history = ledger.history(id),
        rivals = v.rivals.getOrElse(id, Nil),
        alternatives = ledger.alternatives(id).map(Alternative(_, _))))
    }
    val gone = ledger.decisions.keys.toList.sorted.filter(id => !v.ids.contains(id) && ledger.binding(id).isDefined)
      .flatMap(id => ledger.current(id).map(Gone(id, _)))
    Annotated(snapshot, nodes, gone, v.order)

  /** Every node after all it rests on (its parents, the definitions it uses, the contracts its code calls):
    * the order decisions are taken in, a batch's too.
    */
  def order(snapshot: Snapshot): List[NodeId] = structure(snapshot).order

  /** Rejected nodes a proposal says the same as (under another id, or reworded only in its `why`):
    * the developer sees why they were rejected.
    */
  private def resembles(ledger: Ledger, n: SnapNode): List[Resembling] =
    val mine = n.content
    // The same formal content (what Lean checks), however it is worded or named; or the same statement.
    def formal(c: Content) = c.only(Set("sources", "substitutions")).hash
    def same(c: Content) = (formal(c) == formal(mine) && hasFormal(c)) || c.str("statement").exists(st => mine.str("statement").contains(st))
    if ledger.binding(n.id).isDefined then Nil
    else ledger.decisions.toList.sortBy(_._1).flatMap((other, ds) => ds.lastOption.filter(d => other != n.id && d.action == Action.Reject && same(d.content))
      .map(d => Resembling(other, d.reason)))

  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its
    * content as it was then: what is shown for the cause `above`.
    */
  private def moved(snapshot: Snapshot, ledger: Ledger, n: SnapNode): List[Moved] =
    ledger.binding(n.id).filter(d => d.chain != parentChain(snapshot, n) && causes(snapshot, ledger, n).contains(Cause.Above)).fold(Nil) { d =>
      val ids = byId(snapshot)
      def up(x: SnapNode, seen: Set[NodeId]): List[SnapNode] = x.parents.filterNot(seen).flatMap(ids.get).flatMap(p => p :: up(p, seen + p.id))
      // What it rests on: its ancestors, the definitions they use, and the contracts their code calls.
      val above = up(n, Set.empty).distinctBy(_.id)
      (above ++ (n :: above).flatMap(x => x.uses ++ x.relies).distinct.flatMap(ids.get)).distinctBy(_.id).flatMap { a =>
        ledger.history(a.id).filter(x => x.action.binds && x.at <= d.at).lastOption
          .filter(t => meaning(t.content) != meaning(a.content)).map(t => Moved(a.id, t.content))
      }
    }

  private val DefinitionUse = """(?s)^[A-Za-z_]\w* = .*""".r

  /** What the developer decided of a node's content, without what follows from elsewhere: the types
    * it uses (`uses` also lists the definitions it calls, `name = body`, which it says), how its
    * examples print, and a proven implementation.
    */
  private def decidedHash(content: Content, provenImpl: Boolean): Hash =
    // What it says itself (not its edges), with only what the decision recorded.
    val c = ownContent(content)
    val definitions = c("uses").flatMap(_.asArray).fold(Vector.empty[Json])(_.filter(_.asString.exists(DefinitionUse.matches)))
    val examples = c.strs("examples").map(e => Json.fromString(e.takeWhile(_ != ' ') + " — " + e.split(" — ").lastOption.getOrElse("")))
    (c.without(k => k == "uses" || k == "examples" || (provenImpl && k == "implementation")) :+
      ("definitions" -> Json.fromValues(definitions)) :+ ("examples" -> Json.fromValues(examples))).hash
  private def provenImpl(n: SnapNode) = n.implementationProof.exists(_.status == ObligationStatus.Proven)

  /** Why `n` is not mechanical, or None if it is. One rule: a node under review (not a proposal), not
    * a definition or a design node (they hold a choice Lean does not check), where nothing the developer
    * decided of the node itself changed (only what follows from elsewhere moved: the types it uses, a
    * proven implementation, how its examples print, or something above it; a definition it calls is part
    * of what it says), and Lean proves it again; when its parts changed, Lean proves they make it
    * (`complete`) and its tries show nothing wrong with them (none shown not needed, no clash shown).
    */
  def mechanical(snapshot: Snapshot, ledger: Ledger, n: SnapNode): Option[String] =
    val v = view(snapshot, ledger)
    val id = n.id
    val cs = v.causes(n)
    val (ok, total) = n.examplesPassing
    val proven = provenImpl(n)
    if n.kind == NodeKind.Design || n.kind == NodeKind.Definition then Some(s"${n.kind} nodes hold a choice")
    else if v.state(n) != ReviewState.Review then Some(s"$id is ${v.state(n)}: only a node under review can be mechanical")
    else if cs.exists(c => !Set(Cause.Self, Cause.Above, Cause.Parts)(c)) then Some(s"$id is under review for ${cs.mkString(", ")}: the developer decides")
    else if ledger.binding(id).forall(d => decidedHash(d.content, proven) != decidedHash(n.content, proven)) then
      Some(s"what $id says changed: the developer decides")
    else if cs.contains(Cause.Parts) && !partsMake(n) then
      Some(s"$id's parts changed and Lean does not prove they make it, or shows one not needed or a clash: the developer decides")
    else if !Reports.unproven(n).forall(_.startsWith("nothing below proves it")) then Some(s"$id is not proven: only what Lean proves again is mechanical")
    else if ok != total then Some(s"${total - ok} of $id's examples fail")
    else if n.invariants.exists(i => i.status != ObligationStatus.Proven && i.status != ObligationStatus.Exempt) then Some(s"an invariant $id keeps is not proven")
    // Waiting for a node that is itself mechanical is no wait: the batch accepts it first.
    else waitsFor(snapshot, ledger, n).filter(w => v.ids.get(w).forall(x => mechanical(snapshot, ledger, x).isDefined))
      .map(w => s"$id waits for $w")

  /** Lean proves the node's parts make it (`complete`), and its tries ran and show nothing wrong: no part
    * shown not needed (`needed` says only that Lean found no proof without it), no clash shown. The new
    * parts themselves are decided on their own; this settles only that they make the node.
    */
  private def partsMake(n: SnapNode): Boolean = n.split.exists { sp =>
    sp.complete.status == ObligationStatus.Proven && sp.needed.forall(_.status == ObligationStatus.Needed) &&
      sp.clash.status != ObligationStatus.Clash
  }

  /** The decisions below `n` that accepting it can act on, with their reasons, parents first: those
    * accepted (each may be revisited), and those under review only because `n`'s meaning moved
    * (each still holds, or is revisited). Below a node that is under review for anything else,
    * nothing is listed: that node is decided on its own first.
    */
  def below(snapshot: Snapshot, ledger: Ledger, n: SnapNode): List[Below] =
    val id = n.id
    val v = view(snapshot, ledger)
    def accepted(c: SnapNode) = holds(v.state(c)) && ledger.binding(c.id).isDefined
    def row(c: SnapNode, kind: BelowKind) =
      Below(c.id, kind, c.content.statement, reasonNow(ledger, c.id), ledger.chosen(c.id).fold("")(_.reason), c.content.why)
    // Moved only by this node, or by nodes above it already accepted again.
    def movedOnlyBy(c: SnapNode) = v.causes(c) == List(Cause.Above) &&
      moved(snapshot, ledger, c).map(_.id).forall(m => m == id || v.ids.get(m).exists(x => holds(v.state(x))))
    def listed(c: SnapNode): Option[Below] =
      if accepted(c) then Some(row(c, BelowKind.Accepted))
      else if v.state(c) == ReviewState.Review && movedOnlyBy(c) then Some(row(c, BelowKind.Moved)) else None
    // What rests on it, however far down (its parts and theirs; the users of a definition, the callers
    // of a contract, the keepers of an invariant, and what rests on them), through the decisions listed;
    // each once, however many paths lead to it, parents first.
    val seen = mutable.Set(id)
    val found = List.newBuilder[Below]
    var frontier = v.dependents.getOrElse(id, Nil)
    while frontier.nonEmpty do
      val next = frontier.filter(c => seen.add(c.id)).flatMap(c => listed(c).map { r => found += r; c })
      frontier = next.flatMap(c => v.dependents.getOrElse(c.id, Nil))
    val own = found.result().sortBy(b => v.rank.getOrElse(b.id, Int.MaxValue))
    // The idea is what every decision rests on: a root's change lists the decisions outside its tree too.
    val elsewhere =
      if !n.isRoot || n.content("ideaSection").isDefined then Nil
      else snapshot.nodes.filter(c => c.id != id && !own.exists(_.id == c.id) && !isBelow(snapshot, c.id, id) && accepted(c))
        .map(row(_, BelowKind.Accepted))
    // The invariants cut across every concern: a change to a root's idea lists them too.
    val across = if !n.isRoot then Nil
      else snapshot.nodes.filter(c => c.rule && !(own ++ elsewhere).exists(_.id == c.id) && accepted(c)).map(row(_, BelowKind.Accepted))
    own ++ elsewhere ++ across

  /** The reason a node holds now: of its latest change of meaning accepted (the reason it was chosen,
    * if none since); a confirmation (nothing it says changed) adds to it, and never replaces it.
    */
  private def reasonNow(ledger: Ledger, id: NodeId): String =
    val last = ledger.sinceChosen(id).filter(_.action == Action.Accept).lastOption.fold("")(_.reason)
    ledger.binding(id).filter(_.action == Action.Confirm).fold(last)(c => s"$last (since confirmed: ${c.reason})")

  private def isBelow(snapshot: Snapshot, id: NodeId, ancestor: NodeId, seen: Set[NodeId] = Set.empty): Boolean =
    byId(snapshot).get(id).toList.flatMap(_.parents).filterNot(seen).exists(p => p == ancestor || isBelow(snapshot, p, ancestor, seen + p))

  /** The node a decision on `n` waits for: the first of its parents, when `n` rests on them (a proposal, or a
    * node whose parents moved) and it is not accepted.
    */
  def waitsFor(snapshot: Snapshot, ledger: Ledger, n: SnapNode): Option[NodeId] =
    val v = view(snapshot, ledger)
    val restsOnParent = v.state(n) == Proposed || v.causes(n).contains(Cause.Above)
    n.parents.find { p =>
      val ps = v.ids.get(p).map(v.state)
      // Nothing is decided under a parent that is not chosen; what rests on a moved parent waits for it.
      ps.exists(s => s == Proposed || s == Rejected) || (restsOnParent && ps.exists(!holds(_)))
    }.orElse(
      // A node rests on the definitions it uses and the contracts its code calls, as on its parents.
      if !restsOnParent then None else (n.uses ++ n.relies).find(i => v.ids.get(i).exists(x => !holds(v.state(x)))))

  /** Whether two nodes are alternatives to each other: one replaces the other, or both define one term.
    * Parts under one parent are not: together they make it.
    */
  def alternatives(a: SnapNode, b: SnapNode): Boolean =
    a.replaces.contains(b.id) || b.replaces.contains(a.id) || a.defines.intersect(b.defines).nonEmpty

  /** Applies a decision; the new ledger, or why it is refused. */
  def decide(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, at: String, commit: Option[String] = None,
      tree: Option[String] = None): Either[String, Ledger] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: NodeId) = ids.get(id).fold(Proposed)(state(snapshot, l, _))
    def make(action: Action, n: SnapNode, rejected: List[NodeId], reason: String) =
      Decision(action, r.by, at, reason, rejected, code = n.code.map(_.fingerprint), commit = commit, tree = tree,
        chain = parentChain(snapshot, n), content = n.content)
    if r.by.trim.isEmpty then Left("say who decides")
    else if r.action != Action.Accept && r.action != Action.Reject then Left(s"unknown decision ${r.action}: the developer accepts or rejects")
    else if tooFew(r.reason) then
      Left("give the reason for the decision in a few words: it is kept as part of the theory")
    else if ids.get(r.node).exists(n => r.seen.exists(_ != version(snapshot, n))) then
      Left(s"${r.node} changed since you looked at it: look again before deciding")
    else ids.get(r.node) match
      case None =>
        ledger.current(r.node).filter(_ => ledger.binding(r.node).isDefined) match
          case Some(last) =>
            Right(ledger.add(r.node, last.unsigned.copy(action = Action.Remove, by = r.by, at = at, reason = r.reason, rejected = Nil, commit = commit, tree = tree)))
          case None => Left(s"unknown node ${r.node}")
      case Some(n) if r.action == Action.Reject =>
        if st(ledger, r.node) != Proposed then Left(s"${r.node} is ${st(ledger, r.node)}: only a proposal is rejected on its own")
        else
          // The proposals below it rested on it: they go with it.
          def proposedBelow(x: NodeId): List[SnapNode] = view(snapshot, ledger).children.getOrElse(x, Nil)
            .filter(c => st(ledger, c.id) == Proposed).flatMap(c => c :: proposedBelow(c.id))
          Right(proposedBelow(r.node).distinctBy(_.id).foldLeft(ledger.add(r.node, make(Action.Reject, n, Nil, r.reason)))((l, c) =>
            l.add(c.id, make(Action.Reject, c, Nil, s"${r.node}, which it rested on, was rejected: ${r.reason}"))))
      case Some(n) => accept(snapshot, ledger, r, n, make)

  /** Accepting `n`: choosing it (rejecting the alternatives named), accepting a change, or confirming it,
    * with the decisions below named to confirm or revisit.
    */
  private def accept(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, n: SnapNode,
      make: (Action, SnapNode, List[NodeId], String) => Decision): Either[String, Ledger] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: NodeId) = ids.get(id).fold(Proposed)(state(snapshot, l, _))
    val bad = r.reject.filter(x => x == r.node || !ids.get(x).exists(alternatives(n, _)))
    val rejected = r.reject.flatMap(ids.get)
    waitsFor(snapshot, ledger, n) match
      case Some(w) => Left(s"accept $w first: what rests on it is decided after it")
      case None if bad.nonEmpty => Left(s"not an alternative to ${r.node}: ${bad.mkString(", ")}")
      case None if st(ledger, r.node) == Accepted && r.reject.isEmpty && r.confirm.isEmpty && r.revisit.isEmpty =>
        Left(s"${r.node} is already accepted")
      case None =>
        // Choosing (or accepting a change to the node itself) is an acceptance; otherwise a confirmation.
        val cs = causes(snapshot, ledger, n)
        // A change only of what follows from elsewhere (types, printing, proven code) is confirmed: its reason does not replace the node's.
        // A change of its parts only is confirmed too: what it says, and why, stays; its parts are bound with the confirmation.
        val meaningMoved = cs.contains(Cause.Self) && ledger.binding(r.node).forall(d =>
          decidedHash(d.content, provenImpl(n)) != decidedHash(n.content, provenImpl(n)))
        val action = if st(ledger, r.node) == ReviewState.Review && !meaningMoved && r.reject.isEmpty then Action.Confirm else Action.Accept
        val chosen = if st(ledger, r.node) == Accepted && r.reject.isEmpty then ledger
          else ledger.add(r.node, make(action, n, r.reject, r.reason))
        val withRejected = rejected.foldLeft(chosen)((l, x) => l.add(x.id, make(Action.Reject, x, Nil, s"${r.node} was chosen instead: ${r.reason}")))
        // Parents first.
        val first = order(snapshot).zipWithIndex.toMap
        val below = this.below(snapshot, ledger, n)
        val under = below.map(_.id).sortBy(first.getOrElse(_, 0))
        val listed = below.map(b => b.id -> b.kind).toMap
        val notListed = r.revisit.filterNot(listed.contains) ++ r.confirm.filterNot(x => listed.get(x).contains(BelowKind.Moved))
        if notListed.nonEmpty then Left(s"not among the decisions below ${r.node} that this decision can act on: ${notListed.mkString(", ")}")
        else if r.revisit.exists(r.confirm.contains) then Left("a node is either revisited or confirmed")
        else
          // Parents first: a node named to confirm is confirmed once all it rests on (its parents, the
          // definitions it uses, the contracts its code calls) is accepted, and only if it is under review
          // just because something above it moved.
          val tried = under.filter(r.confirm.contains).flatMap(ids.get).foldLeft(Right(withRejected): Either[String, Ledger]) { (acc, c) =>
            acc.flatMap { l =>
              (c.parents ++ c.uses ++ c.relies).filter(ids.contains).find(p => !holds(st(l, p))) match
                case Some(p) => Left(s"${c.id} cannot be confirmed before $p: confirm $p too, or decide ${c.id} after it")
                case None if causes(snapshot, l, c) != List(Cause.Above) =>
                  Left(s"${c.id} is under review for ${causes(snapshot, l, c).mkString(", ")}, not only a change above: decide it on its own")
                case None => Right(l.add(c.id, make(Action.Confirm, c, Nil, s"still holds after ${r.node} changed: ${r.reason}")))
            }
          }
          tried.map(confirmed => r.revisit.distinct.flatMap(ids.get).foldLeft(confirmed)((l, c) =>
            l.add(c.id, make(Action.Revisit, c, Nil, s"${r.node} changed and may affect it: ${r.reason}"))))
