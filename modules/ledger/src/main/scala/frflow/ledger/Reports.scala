package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** The snapshot with the developer's position on each node and what they read to decide it, and the decided nodes gone. */
object Annotate:
  def apply(snapshot: Snapshot, ledger: Ledger): Annotated = apply(Reading(snapshot, ledger))

  def apply(v: Reading): Annotated =
    val l = v.ledger
    val nodes = v.graph.nodes.map { n =>
      val id = n.id
      val st = v.state(n)
      Reviewed(n, Review(state = st, causes = v.causes(n), version = v.version(n), waitsFor = v.waitsFor(n),
        moved = Downstream.moved(v, n), decision = l.chosen(id), binding = l.binding(id),
        reasonNow = l.binding(id).map(_ => Reasons.now(l, id)), notMechanical = v.notMechanical.getOrElse(id, v.mechanical(n)),
        unproven = Proofs.unproven(n),
        rejectedBeside = n.parents.flatMap(l.rejectedUnder).distinctBy(_._1).filter(_._1 != id)
          .map((r, c, why) => RejectedBeside(r, c.statement, c.why, why)),
        below = if st == ReviewState.Accepted then Nil else Downstream.below(v, n),
        history = l.history(id), rivals = v.graph.rivals.getOrElse(id, Nil), alternatives = l.alternatives(id).map(Alternative(_, _))))
    }
    val gone = l.decisions.keys.toList.sorted.filter(id => !v.graph.byId.contains(id) && l.binding(id).isDefined)
      .flatMap(id => l.current(id).map(Gone(id, _)))
    Annotated(v.snapshot, nodes, gone, v.graph.order)

/** What is the agent's to do: replace a rejected node (or remove it), revisit a node, move one resting on a rejected one. */
enum ForAgent derives Codec.AsObject:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])

object Waiting:
  def forAgent(a: Annotated): List[ForAgent] =
    def last(r: Reviewed, action: Action) = r.review.history.reverse.find(_.action == action)
    val rejected = a.nodes.filter(_.state == ReviewState.Rejected)
      .flatMap(r => last(r, Action.Reject).map(d => ForAgent.Replace(r.id, d.by, d.reason)))
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit))
      .map(r => ForAgent.Revisit(r.id, last(r, Action.Revisit).fold("")(_.reason)))
    val moves = a.nodes.map(r => r -> rejectedParents(a, r)).collect { case (r, ps) if ps.nonEmpty => ForAgent.Move(r.id, ps) }
    rejected ++ revisits ++ moves

  /** A node with a parent rejected waits for the agent to move it. */
  def rejectedParents(a: Annotated, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => a.byId.get(p).exists(_.state == ReviewState.Rejected))

  /** The nodes waiting for a developer's decision, in the order to take them. */
  def forDeveloper(a: Annotated): List[Reviewed] =
    val rank = a.order.zipWithIndex.toMap
    a.nodes.filter(r => (r.state == ReviewState.Proposed || r.state == ReviewState.Review) && rejectedParents(a, r).isEmpty)
      .sortBy(r => rank.getOrElse(r.id, Int.MaxValue))

/** How a contract's code is proven: down to its code (a proven define, and the running code), a define not proven yet, or by running. */
enum CodeProof derives Codec.AsObject:
  case ProvenDown(define: String, running: Option[String])
  case Define(name: String, status: ObligationStatus, running: Option[String])
  case ByRunning

object CodeProof:
  def of(n: SnapNode): Option[CodeProof] =
    val impl = n.content.text("implementation")
    val running = impl.linesIterator.find(_.startsWith("runs: ")).map(r => Proofs.runningCode(r.stripPrefix("runs: ")))
    n.implementationProof match
      case Some(p) if p.status == ObligationStatus.Proven => Some(ProvenDown(p.name, running))
      case Some(p) => Some(Define(p.name, p.status, running))
      case None => Option.when(impl.nonEmpty)(ByRunning)

object Proofs:
  /** The CI gate: every node accepted and proven, every example passing; rejected nodes removed from the model, so that
    * nothing rests on them or is governed by them.
    */
  def complete(a: Annotated): Boolean =
    a.gone.isEmpty && a.nodes.forall(r => r.state == ReviewState.Accepted && unproven(r.node).isEmpty)

  /** What of a node is not proven or fails: the one list `status` uses. */
  def unproven(n: SnapNode): List[String] =
    def fine(s: ObligationStatus) = s == ObligationStatus.Proven
    val (ok, total) = n.examplesPassing
    n.status.filterNot(_ == CheckStatus.Proven)
      .map(st => s"its check is $st${n.messages.headOption.fold("")(m => s": ${m.linesIterator.nextOption().getOrElse("")}")}").toList ++
      n.split.map(_.complete).filterNot(c => fine(c.status)).map(c => s"its parts are not proven to make it (${c.status}: ${c.detail})") ++
      n.split.toList.flatMap(_.needed).filter(_.status == ObligationStatus.Shown).map(x => s"${x.id} is not needed for it: ${x.detail}") ++
      n.split.map(_.clash).filter(_.status == ObligationStatus.Shown).map(_ => "its parts contradict each other") ++
      Option.when(n.leaf)("nothing below proves it: add the parts that make it, or a contract") ++
      Option.when(ok != total)(s"${total - ok} example(s) fail") ++
      n.invariants.filterNot(i => fine(i.status) || i.status == ObligationStatus.Exempt).map(i => s"invariant ${i.id} is ${i.status}") ++
      n.implementationProof.filterNot(p => fine(p.status)).map(p => s"its implementation ${p.name} is ${p.status}: not proven to meet the contract") ++
      n.rootImpl.filterNot(p => fine(p.status)).map(p => s"root_impl is ${p.status}: the root is not proven of the code") ++
      n.expectations.filterNot(e => fine(e.status)).map(e => s"an expectation is ${e.status}") ++
      // A root doing nothing meets says only what must not happen: the system can drop every feature unnoticed.
      n.idle.map(what => s"Lean shows doing nothing meets it ($what): say what users can do, so the root is stated as exactly")

  /** Running code as named in a summary: `LoanIndex(...).borrow` as `LoanIndex.borrow`. */
  def runningCode(wiring: String): String =
    val body = wiring.trim.replaceFirst("""^\([^()]*\)\s*=>\s*|^\w+\s*=>\s*""", "")
    val (outside, _) = body.foldLeft(("", 0)) { case ((out, depth), c) =>
      if c == '(' then (out, depth + 1) else if c == ')' then (out, depth - 1) else if depth == 0 then (out + c, depth) else (out, depth)
    }
    val name = outside.replace(".value", "").replaceAll("\\s+", " ").trim
    if name.nonEmpty && name.length <= 60 then name else body.take(57) + "…"

/** Something the theory says that mentions what was asked for. */
enum Mentioned derives Codec.AsObject:
  case Node(id: NodeId)
  case Rejected(id: NodeId, statement: String, reason: String)
  case Gone(id: NodeId)
  case NotModelled(line: String)
  case Idea(line: String)
  case Term(at: NodeId, meaning: String)

/** A mention, with its sentence that holds a word asked for. */
final case class Mention(what: Mentioned, sentence: Option[String]) derives Codec.AsObject

/** Where a change belongs. */
enum Found derives Codec.AsObject:
  /** The nodes governing a file (or a directory, or a file in a directory governed). */
  case Governed(path: String, nodes: List[NodeId])
  /** A source path no node governs: code there changes unnoticed. */
  case Ungoverned(path: String)
  /** What mentions every word asked for (at most ten). */
  case Mentions(query: String, mentions: List[Mention])
  case Nothing(query: String)

object Find:
  def apply(a: Annotated, query: String): Found =
    val q = query.stripPrefix("./")
    def governs(f: String) = f == q || f.startsWith(q.stripSuffix("/") + "/") || q.startsWith(f.stripSuffix("/") + "/")
    val governing = a.nodes.filter(_.node.code.exists(_.files.exists(governs))).map(_.id)
    if governing.nonEmpty then Found.Governed(q, governing)
    else if q.contains('/') || q.endsWith(".scala") then Found.Ungoverned(q)
    else
      // Every word of the query, anywhere in the entry, whatever the case.
      val words = query.toLowerCase.split("\\s+").filter(_.nonEmpty).toList
      def sentence(text: String) =
        text.split("(?<=[.!?])\\s+|\n").find(x => words.exists(x.toLowerCase.contains)).map(_.trim).filter(_.nonEmpty)
      val found = entries(a).filter((_, text) => words.forall(text.toLowerCase.contains)).take(10)
      if found.isEmpty then Found.Nothing(query) else Found.Mentions(query, found.map((m, text) => Mention(m, sentence(text))))

  private def entries(a: Annotated): List[(Mentioned, String)] =
    val ns = a.nodes
    def content(k: String) = ns.flatMap(_.node.content.str(k)).distinct
    def paragraphs(text: String, split: String) = text.split(split).map(_.trim).filter(_.nonEmpty).toList
    val nodes = ns.map(r => Mentioned.Node(r.id) -> (r.id.value :: List("statement", "why").flatMap(r.node.content.str) ++
      r.review.history.map(_.reason)).mkString(" \n"))
    val rejected = ns.flatMap(_.review.rejectedBeside).distinctBy(_.id).filterNot(r => a.byId.contains(r.id))
      .map(r => Mentioned.Rejected(r.id, r.statement, r.reason) -> s"${r.id} ${r.statement} \n${r.why} \n${r.reason}")
    val gone = a.gone.map(g => Mentioned.Gone(g.id) -> s"${g.id} ${g.decision.reason}")
    val notModelled = content("notModelled").flatMap(paragraphs(_, "\n(?=- )")).distinct.map(l => Mentioned.NotModelled(l) -> l)
    val idea = content("idea").flatMap(paragraphs(_, "\n\\s*\n")).filterNot(_.startsWith("#")).distinct.map(l => Mentioned.Idea(l) -> l)
    val terms = ns.flatMap(r => r.node.content.strs("vocabulary").map(r.id -> _)).distinctBy(_._2).map((id, v) => Mentioned.Term(id, v) -> v)
    nodes ++ rejected ++ gone ++ notModelled ++ idea ++ terms

/** IDEA.md as the decisions read it: what a root is decided against, by section, and what is not modelled. */
object Idea:
  /** The `## ` sections but Not modelled, by heading, after the lead (which every section-root is decided against too). */
  def sections(decided: String): (String, List[(String, String)]) =
    val (intro, rest) = decided.linesIterator.toList.span(l => !l.startsWith("## "))
    def go(ls: List[String]): List[(String, String)] = ls match
      case h :: tail =>
        val (body, more) = tail.span(l => !l.startsWith("## "))
        (h.stripPrefix("## ").trim -> (h :: body).mkString("\n").trim) :: go(more)
      case Nil => Nil
    (intro.mkString("\n").trim, go(rest))

  /** The idea a root is decided against, and its `## Not modelled` section. */
  def split(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled")) match
      case -1 => (idea.trim, "")
      case i =>
        val (section, rest) = lines.drop(i + 1).span(l => !(l.startsWith("# ") || l.startsWith("## ")))
        ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)
