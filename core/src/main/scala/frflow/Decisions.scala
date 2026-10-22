package frflow

import frflow.Json.*

/** The developer's position on each node, computed from the snapshot and the ledger, and the one
  * way to record a decision. Shared by the CLI, the browser and the MCP server.
  *
  * The rule: a decision binds a person's reason to the hash of what they saw. Whatever moves
  * under it puts the node back up for review.
  *
  * A snapshot node carries `content` (what the developer sees and decides), its `hash`, its
  * `chain` (its hash with its ancestors') and, if it governs code, a `code` fingerprint.
  *
  * States:
  *   - `proposed`: not decided yet (or rejected, then reworked);
  *   - `accepted`: decided by the developer, and nothing moved since;
  *   - `review`: something moved since it was decided; `causes` say what:
  *     `self` (the node changed), `above` (the meaning of an ancestor changed), `code` (the code
  *     it governs changed), `revisit` (the developer said a change above, such as an edit of the
  *     idea, may affect it), `merged` (two branches decided it, and a merge kept both); a decided
  *     node no longer in the model is listed under `gone`;
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
  import Json.text as s
  private def nodes(snapshot: Json): List[Json] = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
  private def byId(snapshot: Json): Map[String, Json] = structure(snapshot).ids
  private def parentChain(snapshot: Json, n: Json): String = structure(snapshot).parentChain(n)

  /** The snapshot and ledger, with each node's state and causes computed once. */
  private final class View(val snapshot: Json, val ledger: Ledger):
    val all: List[Json] = nodes(snapshot)
    val ids: Map[String, Json] = all.map(n => s(n, "id") -> n).toMap
    val children: Map[String, List[Json]] = all.groupBy(_("parent").flatMap(_.str).getOrElse(""))
    private val states = scala.collection.mutable.Map.empty[String, String]
    private val causeMemo = scala.collection.mutable.Map.empty[String, List[String]]
    // What the node rests on, as the snapshot says (see `Workflow.parentChain`).
    def parentChain(n: Json): String = s(n, "parentChain")
    def causes(n: Json): List[String] = causeMemo.getOrElseUpdate(s(n, "id"), {
      val id = s(n, "id")
      val revisit = ledger.current(id).exists(_.action == "revisit")
      val parentRejected = n("parent").flatMap(_.str).flatMap(ids.get).exists(p => state(p) == "rejected")
      ledger.binding(id).fold(Nil) { d =>
        List("self" -> changed(d, n), "above" -> (d.chain != parentChain(n) || parentRejected),
          "code" -> (d.code != code(n)), "revisit" -> revisit, "merged" -> ledger.forked(id)).collect { case (c, true) => c }
      }
    })
    def state(n: Json): String = states.getOrElseUpdate(s(n, "id"),
      ledger.current(s(n, "id")) match
        case Some(d) if d.action == "reject" => if !changed(d, n) then "rejected" else "proposed"
        case Some(d) if Ledger.binds(d.action) || d.action == "revisit" =>
          if causes(n).nonEmpty then "review" else "accepted"
        case _ => "proposed")

  private var last: View = View(JObj(Nil), Ledger.empty)
  /** What does not depend on the ledger: the last view, if it is of this snapshot. */
  private def structure(snapshot: Json): View = synchronized { if last.snapshot eq snapshot then last else view(snapshot, last.ledger) }
  private def view(snapshot: Json, ledger: Ledger): View = synchronized {
    if !(last.snapshot eq snapshot) || !(last.ledger eq ledger) then last = View(snapshot, ledger)
    last
  }

  /** What FrFlow added to a node's content in later formats: a decision recorded before has none of
    * it, and is not reviewed for it (a new FrFlow needs no decision again).
    */
  private val addedByFormat = Set("definition")

  /** Whether the node says something else than what was decided. */
  private def changed(d: Decision, n: Json): Boolean =
    val missing = addedByFormat.filter(k => d.content(k).isEmpty)
    if missing.isEmpty then d.hash != s(n, "hash")
    else d.hash != Decision.hash(JObj(n("content").map(_.obj).getOrElse(Nil).filterNot(f => missing(f._1))))

  /** The node holds as decided. */
  private def holds(state: String): Boolean = state == "accepted"

  /** What a node rests on: its parent's chain, with the chains of the invariants it keeps and the nodes it relies on. A design
    * decision rests on its parent's place, not its meaning: a change above lists it below, to revisit.
    */
  def above(parentChain: String, invariantChains: List[String]): String =
    if invariantChains.isEmpty then parentChain else sha((parentChain :: invariantChains.sorted)*)

  /** The invariants a node keeps (not those it is exempt from): it rests on their meaning. */
  private def kept(n: Json): List[String] =
    n("invariants").map(_.arr.toList).getOrElse(Nil).filter(i => s(i, "status") != "exempt").flatMap(_("id").flatMap(_.str))
  /** The nodes a node relies on besides its parent: it rests on their meaning too. */
  private def relies(n: Json): List[String] = n("relies").map(_.arr.toList.flatMap(_.str)).getOrElse(Nil)
  private def code(n: Json): String = n("code").flatMap(_("fingerprint")).flatMap(_.str).getOrElse("")
  private def sha(parts: String*): String = Sha.parts(parts*)

  /** A node's chain: what its content means, together with its ancestors'. A change to a node's
    * meaning puts the nodes below up for review; rewording its reason, adding an example, or
    * editing the idea reviews only the node itself.
    */
  def chain(content: Json, parentChain: String): String = sha(meaning(content), parentChain)

  /** What a node's content means, without its reason, examples or idea. */
  def meaning(content: Json): String =
    val parts = Set("parent", "statement", "sources", "substitutions", "vocabulary", "uses", "governs", "formal")
    Decision.hash(JObj(content.obj.filter(f => parts(f._1))))

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
      // To the next heading of its level or above: its `### ` subsections are its own.
      val (section, rest) = lines.drop(i + 1).span(l => !(l.startsWith("# ") || l.startsWith("## ")))
      ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)

  /** What moved under a node's decision. A node whose parent was rejected is reviewed as if its
    * parent's meaning moved: what it rests on is no longer chosen.
    */
  def causes(snapshot: Json, ledger: Ledger, n: Json): List[String] = view(snapshot, ledger).causes(n)

  def state(snapshot: Json, ledger: Ledger, n: Json): String = view(snapshot, ledger).state(n)

  /** What the developer saw of a node: a decision sent with it is refused if the node moved since. */
  def version(snapshot: Json, n: Json): String = sha(s(n, "hash"), parentChain(snapshot, n), code(n)).take(16)

  private def decisionJson(id: String, d: Decision) = obj(
    "node" -> str(id), "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason),
    "rejected" -> JArr(d.rejected.map(str)), "content" -> d.content)

  /** The snapshot with each node's state, what moved, its decision, history and alternatives;
    * and the decided nodes that are gone from the model.
    */
  def annotate(snapshot: Json, ledger: Ledger): Json =
    val ids = byId(snapshot)
    val annotated = nodes(snapshot).map { n =>
      val id = s(n, "id")
      val fields = Seq(
        "state" -> str(state(snapshot, ledger, n)),
        "causes" -> JArr(causes(snapshot, ledger, n).map(str)),
        "version" -> str(version(snapshot, n)),
        "waitsFor" -> waitsFor(snapshot, ledger, n).fold(JNull)(str),
        "moved" -> JArr(moved(snapshot, ledger, n)),
        "decision" -> ledger.chosen(id).fold(JNull)(decisionJson(id, _)),
        "reasonNow" -> (if ledger.binding(id).isDefined then str(reasonNow(ledger, id)) else JNull),
        "mechanical" -> JBool(mechanical(snapshot, ledger, n).isEmpty),
        "notMechanical" -> mechanical(snapshot, ledger, n).fold(JNull)(str),
        "resembles" -> JArr(resembles(ledger, n)),
        "unproven" -> JArr(unproven(n).map(str)),
        // A sibling that says formally the same (variables renamed): the statement may claim more than the spec.
        "sameAs" -> JArr(structure(snapshot).children.getOrElse(n("parent").flatMap(_.str).getOrElse(""), Nil).filter { m =>
          s(m, "id") != id && s(m, "kind") == s(n, "kind") && m("content").flatMap(_("sources")).exists(_.obj.nonEmpty) &&
            m("content").flatMap(_("sources")).map(alpha) == n("content").flatMap(_("sources")).map(alpha)
        }.map(m => str(s(m, "id")))),
        "rejectedBeside" -> JArr(n("parent").flatMap(_.str).toList.flatMap(ledger.rejectedUnder).filter(_._1 != id).map((r, c, why) =>
          obj("id" -> str(r), "statement" -> c("statement").getOrElse(str("")), "why" -> c("why").getOrElse(str("")), "reason" -> str(why)))),
        "below" -> JArr(if state(snapshot, ledger, n) == "accepted" then Nil else below(snapshot, ledger, n)),
        "history" -> JArr(ledger.history(id).map(decisionJson(id, _))),
        "alternatives" -> JArr(ledger.alternatives(id).map((a, c) => obj("id" -> str(a), "content" -> c))))
      JObj(n.obj.filterNot(f => fields.exists(_._1 == f._1)) ++ fields)
    }
    val gone = ledger.decisions.toList.sortBy(_._1).collect {
      case (id, ds) if !ids.contains(id) && ledger.binding(id).isDefined && !ledger.renames.contains(id) =>
        // A proposal that says what it said, under another name: it may be the same node, renamed.
        val renamedTo = nodes(snapshot).filter(p => !ledger.decisions.contains(s(p, "id")) &&
          sameRenamed(ledger, ledger.binding(id).get.content, p("content").getOrElse(JNull),
            renaming(id, ledger.binding(id).get.content, s(p, "id"), p("content").getOrElse(JNull)))).map(p => str(s(p, "id")))
        obj("id" -> str(id), "decision" -> decisionJson(id, ds.last), "renamedTo" -> JArr(renamedTo))
    }
    JObj(snapshot.obj.filterNot(f => Set("nodes", "gone", "order")(f._1)) ++ Seq("nodes" -> JArr(annotated), "gone" -> JArr(gone),
      "order" -> JArr(order(snapshot).map(str))))

  /** A node's content as decided, with the ids renamed since (and those of `more`) written as they are
    * now: equal to its content now when nothing but names changed.
    */
  def sameRenamed(ledger: Ledger, decided: Json, now: Json, more: Map[String, String] = Map.empty): Boolean =
    val renames = ledger.renames.toList.flatMap((o, n) => ledger.binding(o).zip(ledger.decisions.get(n).flatMap(_.headOption))
      .fold(Map(o -> n))((a, b) => renaming(o, a.content, n, b.content))).toMap ++ more
    def go(j: Json): Json = j match
      case JStr(x) => JStr(renames.foldLeft(x)((t, r) => t.replaceAll(s"\\b${java.util.regex.Pattern.quote(r._1)}\\b", java.util.regex.Matcher.quoteReplacement(r._2))))
      case JArr(xs) => JArr(xs.map(go))
      case JObj(fs) => JObj(fs.map((k, v) => k -> go(v)))
      case other => other
    renames.nonEmpty && Decision.hash(go(decided)) == Decision.hash(now)

  /** A rename: the id, and the name of the Scala value that defines the node, when that changed too. */
  def renaming(from: String, before: Json, to: String, after: Json): Map[String, String] =
    def valName(c: Json) = c("definition").flatMap(_.str).flatMap(d => """^\s*(?:lazy\s+)?(?:val|def)\s+([A-Za-z_][A-Za-z0-9_]*)""".r.findFirstMatchIn(d)).map(_.group(1))
    Map(from -> to) ++ valName(before).zip(valName(after)).filter(_ != _).toMap

  /** Every node after all it rests on (its parent, the invariants it keeps, the nodes it relies on):
    * the order decisions are taken in, a batch's too.
    */
  def order(snapshot: Json): List[String] =
    val ns = nodes(snapshot)
    val ids = ns.map(s(_, "id")).toSet
    def on(n: Json) = (n("parent").flatMap(_.str).toList ++ kept(n) ++ relies(n)).filter(ids)
    val byId = ns.map(n => s(n, "id") -> n).toMap
    val done = scala.collection.mutable.LinkedHashSet.empty[String]
    def visit(id: String, seen: Set[String]): Unit =
      if !done(id) && !seen(id) then
        byId.get(id).foreach(n => on(n).foreach(visit(_, seen + id)))
        done += id
    ns.foreach(n => visit(s(n, "id"), Set.empty))
    done.toList

  /** Rejected nodes a proposal says the same as (under another id, or reworded only in its `why`):
    * the developer sees why they were rejected.
    */
  private def resembles(ledger: Ledger, n: Json): List[Json] =
    val id = s(n, "id")
    val mine = n("content").getOrElse(JNull)
    // The same formal content (what Lean checks), however it is worded, named, or its variables are
    // called; or the same statement.
    def formal(c: Json) = Decision.hash(alpha(JObj(c.obj.filter(f => Set("sources", "substitutions")(f._1)))))
    def same(c: Json) = (formal(c) == formal(mine) && (c("sources").exists(_.obj.nonEmpty) || c("substitutions").exists(_.arr.nonEmpty))) ||
      c("statement").flatMap(_.str).exists(st => mine("statement").flatMap(_.str).contains(st))
    if ledger.binding(id).isDefined then Nil
    else ledger.decisions.toList.sortBy(_._1).flatMap((other, ds) => ds.lastOption.filter(d => other != id && d.action == "reject" && same(d.content))
      .map(d => obj("id" -> str(other), "reason" -> str(d.reason))))

  /** Source text with its bound variables renamed in order (`x`, `user` become `v0`, `v1`) and spacing
    * normalized: two lambdas that differ only in their variables' names read the same.
    */
  def alpha(j: Json): Json = j match
    case JStr(src) =>
      val binder = """(?<![\w.])([A-Za-z_]\w*)(?=\s*(?::[^,()=]+)?\s*(?:,[^()]*)?\)?\s*=>)""".r
      val names = binder.findAllMatchIn(src).map(_.group(1)).toList.distinct
      val renamed = names.zipWithIndex.foldLeft(src) { case (t, (n, i)) =>
        t.replaceAll(s"(?<![\\w.])${java.util.regex.Pattern.quote(n)}(?!\\w)", s"v$i")
      }
      JStr(renamed.replaceAll("\\s+", " ").trim)
    case JArr(xs) => JArr(xs.map(alpha))
    case JObj(fs) => JObj(fs.map((k, v) => k -> alpha(v)))
    case other => other

  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its
    * content as it was then: what the browser shows for the cause `above`.
    */
  private def moved(snapshot: Json, ledger: Ledger, n: Json): List[Json] =
    ledger.binding(s(n, "id")).filter(_.chain != parentChain(snapshot, n)).fold(Nil) { d =>
      val ids = byId(snapshot)
      def up(x: Json): List[Json] = x("parent").flatMap(_.str).flatMap(ids.get).fold(Nil)(p => p :: up(p))
      // What it rests on: its ancestors, the invariants it keeps, and what it and its ancestors rely on.
      (up(n) ++ (kept(n) ++ (n :: up(n)).flatMap(relies)).distinct.flatMap(ids.get)).flatMap { a =>
        val id = s(a, "id")
        val then_ = ledger.history(id).filter(x => Ledger.binds(x.action) && x.at <= d.at).lastOption
        val now = a("content").getOrElse(JNull)
        then_.filter(t => meaning(t.content) != meaning(now)).map(t => obj("id" -> str(id), "before" -> t.content))
      }
    }

  /** Every decision, newest first: the history of the theory. */
  def history(ledger: Ledger): Json = JArr(ledger.all.map(decisionJson(_, _)))

  /** A decision. `action` is `accept` (choose the node, rejecting the alternatives in `reject`;
    * accept it again after something moved; agree that a gone node is gone) or `reject` (reject a
    * proposal, choosing nothing instead).
    *
    * Accepting a change, the developer goes through the decisions below, with their reasons: those
    * the change may affect go to `revisit` (reviewed again); those under review only because this
    * node's meaning moved, and not affected, go to `confirm` (they still hold). Nothing below is
    * confirmed unless named. `seen` is the node's `version` as the developer saw it; the decision is
    * refused if the node moved since.
    */
  final case class Request(node: String, by: String, reason: String, reject: List[String] = Nil,
      revisit: List[String] = Nil, confirm: List[String] = Nil, action: String = "accept", seen: String = "",
      held: List[String] = Nil, from: String = "")

  /** A row of `below`: whether its reasons say when to revisit it, so it is answered by name. */
  private def revisitFields(ledger: Ledger, c: Json): Seq[(String, Json)] =
    val id = s(c, "id")
    Seq("conditional" -> JBool((reasonNow(ledger, id) :: ledger.chosen(id).fold("")(_.reason) ::
      c("content").flatMap(_("why")).flatMap(_.str).toList).exists(conditional)))
  extension (j: Json) private def ++(fs: Seq[(String, Json)]): Json = JObj(j.obj ++ fs)

  /** A reason (or why) that says when to revisit the decision: such a decision below a change is
    * answered by name, still holds or revisit, never left to a default.
    */
  def conditional(text: String): Boolean =
    """(?i)\b(revisit|reconsider)\b(\s+\w+){0,3}\s+(if|when|once)\b|\bunless\b|\buntil\b|\bas long as\b|\bonly while\b""".r.findFirstIn(text).isDefined

  /** Why `n` is not mechanical, or None if it is. One rule: a node under review (not a proposal) of a
    * kind that holds no choice of meaning (a refinement, a contract, an invariant), where nothing the
    * developer decided changed (only what follows from elsewhere moved: the types it uses, a proven
    * implementation, how its examples print, or something above it), and Lean proves it again.
    */
  def mechanical(snapshot: Json, ledger: Ledger, n: Json): Option[String] =
    val v = view(snapshot, ledger)
    val id = s(n, "id")
    val kind = s(n, "kind")
    val cs = v.causes(n)
    val (ok, total) = examples(n)
    val provenImpl = n("implementationProof").exists(p => p != JNull && s(p, "status") == "proven")
    // What the developer decided, without what follows from elsewhere.
    def decided(c: Json) = Decision.hash(JObj(c.obj.filterNot(f => f._1 == "uses" || f._1 == "examples" || (provenImpl && f._1 == "implementation")) :+
      ("examples" -> JArr(c("examples").map(_.arr.toList.flatMap(_.str)).getOrElse(Nil).map(e => str(e.takeWhile(_ != ' ') + " — " + e.split(" — ").lastOption.getOrElse("")))))))
    if !Set("refine", "contract", "invariant")(kind) then Some(s"$kind nodes hold a choice")
    else if v.state(n) != "review" then Some(s"$id is ${v.state(n)}: only a node under review can be mechanical")
    else if cs.exists(c => c != "self" && c != "above") then Some(s"$id is under review for ${cs.mkString(", ")}: the developer decides")
    else if ledger.binding(id).forall(d => decided(d.content) != decided(n("content").getOrElse(JNull))) then Some(s"what $id says changed: the developer decides")
    else if kind != "invariant" && !n("link").filter(_ != JNull).map(s(_, "status")).contains("proven") then Some(s"$id's link is not proven: only what Lean proves again is mechanical")
    else if ok != total then Some(s"${total - ok} of $id's examples fail")
    else if n("invariants").exists(_.arr.exists(i => !Set("proven", "exempt")(s(i, "status")))) then Some(s"an invariant $id keeps is not proven")
    // Waiting for a node that is itself mechanical is no wait: the batch accepts it first.
    else if waitsFor(snapshot, ledger, n).exists(w => v.ids.get(w).forall(x => mechanical(snapshot, ledger, x).isDefined)) then
      Some(s"$id waits for ${waitsFor(snapshot, ledger, n).get}")
    else None

  /** The decisions below `n` that accepting it can act on, with their reasons, parents first: those
    * accepted (each may be revisited), and those under review only because `n`'s meaning moved
    * (each still holds, or is revisited). Below a node that is under review for anything else,
    * nothing is listed: that node is decided on its own first.
    */
  def below(snapshot: Json, ledger: Ledger, n: Json): List[Json] =
    val id = s(n, "id")
    def children(x: String) = view(snapshot, ledger).children.getOrElse(x, Nil)
    // Moved only by this node, or by nodes above it already accepted again.
    def movedOnlyBy(c: Json) = causes(snapshot, ledger, c) == List("above") &&
      moved(snapshot, ledger, c).flatMap(_("id").flatMap(_.str)).forall(m => m == id || byId(snapshot).get(m).exists(x => holds(state(snapshot, ledger, x))))
    def go(x: String): List[Json] = children(x).flatMap { c =>
      val cid = s(c, "id")
      val st = state(snapshot, ledger, c)
      val kind = if holds(st) && ledger.binding(cid).isDefined then Some("accepted")
        else if st == "review" && movedOnlyBy(c) then Some("moved") else None
      kind.toList.flatMap { k =>
        (obj("id" -> str(cid), "kind" -> str(k), "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")),
          "reason" -> str(reasonNow(ledger, cid)), "chosen" -> str(ledger.chosen(cid).fold("")(_.reason))) ++ revisitFields(ledger, c)) :: go(cid)
      }
    }
    // Below an invariant: the nodes that keep it, or are exempt from it; below any node, those relying on it.
    val related =
      nodes(snapshot).filter(c => (s(n, "kind") == "invariant" && c("invariants").exists(_.arr.exists(i => s(i, "id") == id))) ||
        relies(c).contains(id)).flatMap { c =>
        val cid = s(c, "id")
        val st = state(snapshot, ledger, c)
        val kind = if holds(st) && ledger.binding(cid).isDefined then Some("accepted") else if st == "review" && movedOnlyBy(c) then Some("moved") else None
        kind.map(k => obj("id" -> str(cid), "kind" -> str(k), "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")),
          "reason" -> str(reasonNow(ledger, cid)), "chosen" -> str(ledger.chosen(cid).fold("")(_.reason))) ++ revisitFields(ledger, c))
      }
    val down = go(id)
    val own = down ++ related.filterNot(r => down.exists(d => s(d, "id") == s(r, "id")))
    // The idea is what every decision rests on: a root's change lists the decisions outside its tree too.
    val elsewhere =
      if s(n, "kind") != "root" || n("content").flatMap(_("ideaSection")).isDefined then Nil
      else nodes(snapshot).filter { c =>
        val cid = s(c, "id")
        cid != id && !own.exists(b => s(b, "id") == cid) && !isBelow(snapshot, cid, id) &&
          holds(state(snapshot, ledger, c)) && ledger.binding(cid).isDefined
      }.map(c => obj("id" -> str(s(c, "id")), "kind" -> str("accepted"),
        "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")), "reason" -> str(reasonNow(ledger, s(c, "id"))), "chosen" -> str(ledger.chosen(s(c, "id")).fold("")(_.reason))) ++ revisitFields(ledger, c))
    // The invariants cut across every concern: a change to a root's idea lists them too.
    val across = if s(n, "kind") != "root" then Nil else nodes(snapshot).filter { c =>
      s(c, "kind") == "invariant" && !(own ++ elsewhere).exists(b => s(b, "id") == s(c, "id")) && holds(state(snapshot, ledger, c)) && ledger.binding(s(c, "id")).isDefined
    }.map(c => obj("id" -> str(s(c, "id")), "kind" -> str("accepted"), "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")),
      "reason" -> str(reasonNow(ledger, s(c, "id"))), "chosen" -> str(ledger.chosen(s(c, "id")).fold("")(_.reason))) ++ revisitFields(ledger, c))
    // With each its why: the theory a change may undo is often written there, not in the reason.
    val all = byId(snapshot)
    (own ++ elsewhere ++ across).map(b => JObj(b.obj :+ ("why" -> all.get(s(b, "id")).flatMap(_("content")).flatMap(_("why")).getOrElse(str("")))))

  /** What a diff of governed code may touch that no proof covers: the invariants whose domain types it
    * names (with why each was decided), and the parameters it binds anew (with what each means). Shown
    * with every code review.
    */
  def codeNotes(snapshot: Json, diff: String): List[String] =
    val changed = diff.linesIterator.filter(l => (l.startsWith("+") || l.startsWith("-")) && !l.startsWith("+++") && !l.startsWith("---")).mkString("\n")
    def mentions(w: String) = w.nonEmpty && s"(?<![\\w])${java.util.regex.Pattern.quote(w)}(?![\\w])".r.findFirstIn(changed).isDefined
    val invs = nodes(snapshot).filter(c => s(c, "kind") == "invariant").flatMap { i =>
      val types = i("content").flatMap(_("uses")).map(_.arr.toList.flatMap(_.str)).getOrElse(Nil)
        .flatMap(u => """^(?:case class|enum)\s+(\w+)""".r.findFirstMatchIn(u).map(_.group(1)))
      types.find(mentions).map(t => s"the change names $t, which the invariant ${s(i, "id")} is about: does it show one to someone the rule refuses? (${i("content").flatMap(_("statement")).flatMap(_.str).getOrElse("")})")
    }
    // A parameter whose binding changed: what it is bound to differs between the lines removed and added.
    def binds(lines: Iterator[String], name: String) =
      val re = s"(?<![\\w])${java.util.regex.Pattern.quote(name)}\\.bind(?:Table)?\\(([^)]*)\\)".r
      lines.flatMap(l => re.findAllMatchIn(l).map(_.group(1).trim)).toSet
    def side(c: Char) = diff.linesIterator.filter(l => l.startsWith(c.toString) && !l.startsWith(s"$c$c$c"))
    val params = snapshot("params").map(_.arr.toList).getOrElse(Nil).filter(p => binds(side('-'), s(p, "name")) != binds(side('+'), s(p, "name")))
      .map(p => s"it binds ${s(p, "name")}, which means: ${s(p, "means")} — does the new value still mean that?")
    invs ++ params

  /** The reason a node holds now: of its latest acceptance (a confirmation adds to it, so with it). */
  private def reasonNow(ledger: Ledger, id: String): String =
    // The reason it was chosen first: a later change accepted (a batch of type changes, say) adds to it.
    val accepts = ledger.sinceChosen(id).filter(_.action == "accept")
    val chosen = accepts.headOption.fold("")(_.reason)
    val last = accepts.lastOption.map(_.reason).filter(_ != chosen).fold(chosen)(l => s"$chosen (latest change: $l)")
    ledger.binding(id).filter(_.action == "confirm").fold(last)(c => s"$last (since confirmed: ${c.reason})")

  private def isBelow(snapshot: Json, id: String, ancestor: String): Boolean =
    structure(snapshot).ids.get(id).flatMap(_("parent").flatMap(_.str)).exists(p => p == ancestor || isBelow(snapshot, p, ancestor))

  /** The node a decision on `n` waits for: its parent, when `n` rests on it (a proposal, or a node
    * whose parent moved) and the parent is not accepted.
    */
  def waitsFor(snapshot: Json, ledger: Ledger, n: Json): Option[String] =
    val restsOnParent = state(snapshot, ledger, n) == "proposed" || causes(snapshot, ledger, n).contains("above")
    n("parent").flatMap(_.str).filter { p =>
      val ps = byId(snapshot).get(p).map(state(snapshot, ledger, _))
      // Nothing is decided under a parent that is not chosen; what rests on a moved parent waits for it.
      ps.exists(Set("proposed", "rejected")) || (restsOnParent && ps.exists(!holds(_)))
    }.orElse(
      // A contract rests on the invariants it keeps, and a node on what it relies on, as on its parent.
      if !restsOnParent then None else (kept(n) ++ relies(n)).find(i => byId(snapshot).get(i).exists(x => !holds(state(snapshot, ledger, x)))))

  /** Applies a decision; the new ledger, or why it is refused. */
  def decide(snapshot: Json, ledger: Ledger, r: Request, at: String, commit: String = "", tree: String = ""): Either[String, Ledger] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: String) = state(snapshot, l, ids(id))
    def make(action: String, n: Json, rejected: List[String], reason: String) =
      Decision(action, n("content").getOrElse(JNull), parentChain(snapshot, n), r.by, at, reason, rejected, code(n), commit, tree)
    if r.by.trim.isEmpty then Left("say who decides")
    else if !Set("accept", "reject", "rename")(r.action) then Left(s"unknown decision ${r.action}")
    else if Words.tooFew(r.reason) then
      Left("give the reason for the decision in a few words: it is kept as part of the theory")
    else if ids.get(r.node).exists(n => r.seen.nonEmpty && r.seen != version(snapshot, n)) then
      Left(s"${r.node} changed since you looked at it: look again before deciding")
    else if r.action == "rename" then
      // The proposal is the gone node, renamed: it continues its history (its choice, reasons and
      // the alternatives rejected for it) in one decision.
      if !ids.contains(r.node) || ledger.decisions.contains(r.node) then Left(s"only a new proposal is a renamed node: ${r.node} is not one")
      else if ids.contains(r.from) || ledger.binding(r.from).isEmpty || ledger.renames.contains(r.from) then Left(s"${r.from} is not a decided node gone from the model")
      else if !sameRenamed(ledger, ledger.binding(r.from).get.content, ids(r.node)("content").getOrElse(JNull),
          renaming(r.from, ledger.binding(r.from).get.content, r.node, ids(r.node)("content").getOrElse(JNull))) then
        Left(s"${r.node} says something else than ${r.from} did, not only under another name: decide it as a new node")
      else Right(ledger.add(r.node, make("accept", ids(r.node), Nil, s"renamed from ${r.from}: ${r.reason}").copy(from = r.from)))
    else if !ids.contains(r.node) then
      ledger.current(r.node) match
        case Some(last) if ledger.binding(r.node).isDefined =>
          Right(ledger.add(r.node, last.unsigned.copy(action = "remove", by = r.by, at = at, reason = r.reason, rejected = Nil, commit = commit, tree = tree)))
        case _ => Left(s"unknown node ${r.node}")
    else
      val n = ids(r.node)
      val parent = n("parent").flatMap(_.str)
      val bad = r.reject.filter(x => x == r.node || !ids.get(x).exists(_("parent").flatMap(_.str) == parent))
      if r.action == "reject" then
        if st(ledger, r.node) != "proposed" then Left(s"${r.node} is ${st(ledger, r.node)}: only a proposal is rejected on its own")
        else
          // The proposals below it rested on it: they go with it.
          def proposedBelow(x: String): List[String] = view(snapshot, ledger).children.getOrElse(x, Nil)
            .filter(c => st(ledger, s(c, "id")) == "proposed").flatMap(c => s(c, "id") :: proposedBelow(s(c, "id")))
          Right(proposedBelow(r.node).foldLeft(ledger.add(r.node, make("reject", n, Nil, r.reason)))((l, x) =>
            l.add(x, make("reject", ids(x), Nil, s"${r.node}, which it rested on, was rejected: ${r.reason}"))))
      else if waitsFor(snapshot, ledger, n).isDefined then
        Left(s"accept ${waitsFor(snapshot, ledger, n).get} first: what rests on it is decided after it")
      else if bad.nonEmpty then Left(s"not an alternative to ${r.node}: ${bad.mkString(", ")}")
      else if st(ledger, r.node) == "accepted" && r.reject.isEmpty && r.confirm.isEmpty && r.revisit.isEmpty then
        Left(s"${r.node} is already accepted")
      else
        // Choosing (or accepting a change to the node itself) is an acceptance; otherwise a confirmation.
        val cs = causes(snapshot, ledger, n)
        val action = if st(ledger, r.node) == "review" && !cs.contains("self") && r.reject.isEmpty then "confirm" else "accept"
        val chosen = if st(ledger, r.node) == "accepted" && r.reject.isEmpty then ledger
          else ledger.add(r.node, make(action, n, r.reject, r.reason))
        val withRejected = r.reject.foldLeft(chosen)((l, x) => l.add(x, make("reject", ids(x), Nil, s"${r.node} was chosen instead: ${r.reason}")))
        // Parents first, as listed below the node.
        val under = below(snapshot, ledger, n).map(b => s(b, "id"))
        val listed = below(snapshot, ledger, n).map(b => s(b, "id") -> s(b, "kind")).toMap
        val notListed = r.revisit.filterNot(listed.contains) ++ r.confirm.filterNot(x => listed.get(x).contains("moved"))
        // Those whose reason says when to revisit them are answered one by one.
        val conditions = below(snapshot, ledger, n).filter(b => s(b, "kind") == "accepted" && b("conditional").contains(JBool(true)))
          .map(b => s(b, "id")).filterNot(x => r.revisit.contains(x) || r.confirm.contains(x) || r.held.contains(x))
        if notListed.nonEmpty then Left(s"not among the decisions below ${r.node} that this decision can act on: ${notListed.mkString(", ")}")
        else if r.revisit.exists(r.confirm.contains) then Left("a node is either revisited or confirmed")
        else if conditions.nonEmpty then
          Left(s"say for each decision below that names when to revisit it whether it still holds or is revisited: ${conditions.mkString(", ")}")
        else
          // Parents first: a node named to confirm is confirmed once its parent is accepted, and only
          // if it is under review just because something above it moved.
          val confirmed = under.filter(r.confirm.contains).foldLeft(withRejected) { (l, id) =>
            val c = ids(id)
            val parentAccepted = c("parent").flatMap(_.str).forall(p => holds(st(l, p)))
            if parentAccepted && st(l, id) == "review" && causes(snapshot, l, c) == List("above") then
              l.add(id, make("confirm", c, Nil, s"still holds after ${r.node} changed: ${r.reason}"))
            else l
          }
          // The decisions listed and left as they are were considered: say so on this decision.
          val held = listed.collect { case (x, "accepted") if !r.revisit.contains(x) => x }.toList.sorted
          val withHeld = if held.isEmpty || !confirmed.current(r.node).exists(_.at == at) then confirmed
            else confirmed.copy(decisions = confirmed.decisions.updated(r.node,
              confirmed.history(r.node).init :+ confirmed.history(r.node).last.copy(held = held)))
          Right(r.revisit.distinct.foldLeft(withHeld)((l, id) =>
            l.add(id, make("revisit", ids(id), Nil, s"${r.node} changed and may affect it: ${r.reason}"))))

  // -- views: the same for the CLI, the browser and the agent ---------------------------------

  private def examples(n: Json): (Int, Int) =
    val ex = n("examples").map(_.arr.toList).getOrElse(Nil)
    (ex.count(e => s(e, "contract") == "ok" && e("implementation").forall(i => i == JNull || i.str.contains("ok"))), ex.size)

  /** The tree as text: each node's state (and what moved), its link to the parent, its examples. */
  def tree(annotated: Json, mark: Option[String] = None): String =
    val ns = nodes(annotated)
    def go(n: Json, depth: Int): List[String] =
      val cs = n("causes").map(_.arr.flatMap(_.str)).getOrElse(Nil)
      val st = if cs.nonEmpty then s"review: ${cs.mkString(", ")}"
        else if s(n, "state") == "rejected" then "rejected: remove it from the model"
        else s(n, "state")
      val link = n("link").filter(_ != JNull).fold("") { l => s", link ${s(l, "status")}${if s(l, "detail").nonEmpty then s" (${s(l, "detail")})" else ""}" }
      val (ok, total) = examples(n)
      val ex = if total == 0 then "" else s", examples $ok/$total"
      val all = n("invariants").map(_.arr.toList).getOrElse(Nil)
      val (exempt, kept) = all.partition(i => s(i, "status") == "exempt")
      val keeps = (if kept.isEmpty then "" else s", keeps ${kept.map(i => s"${s(i, "id")} ${s(i, "status")}").mkString(", ")}") +
        (if exempt.isEmpty then "" else s", exempt from ${exempt.map(s(_, "id")).mkString(", ")}")
      val impl = n("implementationProof").filter(_ != JNull).fold("")(p => s", implementation ${s(p, "status")}")
      val covers = n("covers").map(_.arr.flatMap(_.str).toList).filter(_.nonEmpty).fold("")(cs => s", kept by ${cs.mkString(", ")}")
      val exps = n("expectations").map(_.arr.toList).getOrElse(Nil).filter(e => s(e, "status") != "informal")
      val notProven = exps.filter(e => s(e, "status") != "proven")
      val expects = if exps.isEmpty then "" else if notProven.isEmpty then s", expectations ${exps.size}/${exps.size} proven"
        else s", expectations ${exps.size - notProven.size}/${exps.size} proven (${notProven.map(e => s"${s(e, "status")}: \"${s(e, "statement").take(80)}\"").mkString("; ")})"
      val here = if mark.contains(s(n, "id")) then "   ← this node" else ""
      s"${"  " * depth}${s(n, "id")} (${s(n, "kind")})  [$st$link$ex$expects$keeps$impl$covers]$here" ::
        ns.filter(_("parent").flatMap(_.str).contains(s(n, "id"))).flatMap(go(_, depth + 1))
    val gone = annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => s"${s(g, "id")}  [review: gone]")
    (ns.filter(_("parent").forall(_ == JNull)).flatMap(go(_, 0)) ++ gone).mkString("\n")

  /** Where a change belongs: the nodes governing a file, or those whose id, statement or reasons
    * mention the words asked for, best first.
    */
  def find(annotated: Json, query: String): String =
    val ns = nodes(annotated)
    def files(n: Json) = n("code").filter(_ != JNull).flatMap(_("files")).map(_.arr.flatMap(_.str).toList).getOrElse(Nil)
    def line(n: Json) = s"- ${s(n, "id")} (${s(n, "kind")}, ${s(n, "state")}): ${n("content").flatMap(_("statement")).flatMap(_.str).getOrElse("")}"
    val q = query.stripPrefix("./")
    val governing = ns.filter(n => files(n).exists(f => f == q || f.startsWith(q.stripSuffix("/") + "/") || q.startsWith(f.stripSuffix("/") + "/")))
    if governing.nonEmpty then ("Governed by:" :: governing.map(line)).mkString("\n")
    else if q.contains('/') || q.endsWith(".scala") then
      s"No node governs $q: code there changes unnoticed (status fails on it). Give it an owner: the contract whose implementation it is, `.governing`, or a design node."
    else
      // Everything the theory says, as entries: the nodes (with their reasons), the options rejected
      // (gone from the model or not), the gone nodes, and the lines of what is not modelled.
      final case class Entry(label: String, text: String)
      val nodeEntries = ns.map(n => Entry(line(n), (s(n, "id") :: List("statement", "why").flatMap(k => n("content").flatMap(_(k)).flatMap(_.str)) ++
        n("history").map(_.arr.toList).getOrElse(Nil).map(h => s(h, "reason"))).mkString(" \n")))
      val rejected = ns.flatMap(_("rejectedBeside").map(_.arr.toList).getOrElse(Nil)).distinctBy(r => s(r, "id"))
        .filterNot(r => ns.exists(n => s(n, "id") == s(r, "id")))
        .map(r => Entry(s"- rejected ${s(r, "id")}: ${s(r, "statement")} — rejected because: ${s(r, "reason")}", s"${s(r, "id")} ${s(r, "statement")} \n${s(r, "why")} \n${s(r, "reason")}"))
      val gone = annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => Entry(s"- gone ${s(g, "id")}", s"${s(g, "id")} ${g("decision").flatMap(_("reason")).flatMap(_.str).getOrElse("")}"))
      val notModelled = nodes(annotated).flatMap(_("content").flatMap(_("notModelled")).flatMap(_.str)).distinct
        .flatMap(_.split("\n(?=- )").map(_.trim).filter(_.nonEmpty)).distinct.map(l => Entry(s"- not modelled: ${l.replaceAll("\\s+", " ")}", l))
      // The idea's lines and the terms' meanings say what the model is about too.
      val ideaLines = nodes(annotated).flatMap(_("content").flatMap(_("idea")).flatMap(_.str)).distinct
        .flatMap(_.split("\n\\s*\n").map(_.trim).filter(l => l.nonEmpty && !l.startsWith("#"))).distinct
        .map(l => Entry(s"- idea: ${l.replaceAll("\\s+", " ").take(160)}", l))
      val terms = nodes(annotated).flatMap(n => n("content").flatMap(_("vocabulary")).map(_.arr.toList.flatMap(_.str)).getOrElse(Nil).map(v => s(n, "id") -> v))
        .distinctBy(_._2).map((id, v) => Entry(s"- term (at $id): $v", v))
      val all = nodeEntries ++ rejected ++ gone ++ notModelled ++ ideaLines ++ terms
      // Words compared by their stem: "expiry", "expire" and "expired" find each other.
      def stem(w: String) = w.toLowerCase.replaceAll("(ies|ied|ying|ing|ed|es|s|y|e)$", "")
      val words = query.toLowerCase.split("\\W+").filter(_.length > 2).map(stem).filter(_.length > 2).toList.distinct
      def has(e: Entry, w: String) = e.text.toLowerCase.contains(w)
      // A word every entry has says little: rarer words weigh more.
      def weight(w: String) = math.log((all.size + 1).toDouble / (1 + all.count(has(_, w))))
      val scored = all.map(e => e -> words.filter(has(e, _)).map(weight).sum).filter(_._2 > 0.01).sortBy(-_._2).take(10)
      def sentence(e: Entry) = e.text.split("(?<=[.!?])\\s+|\n").find(x => words.exists(x.toLowerCase.contains)).map(_.trim).filter(_.nonEmpty)
      if scored.isEmpty then s"No node, rejected option or not-modelled line mentions \"$query\": a new concern may need a new node (and a governed home for its code)."
      else ("What mentions it, best first:" :: scored.map((e, _) => e.label + sentence(e).filterNot(e.label.contains).fold("")(x => s"\n    \"${x.take(200)}\""))).mkString("\n")

  /** What waits on whom: decisions for the developer, clean-up for the agent. */
  def waiting(annotated: Json): (List[String], List[String]) =
    val ns = nodes(annotated)
    val ids = byId(annotated)
    // A node resting on a rejected node waits for the agent to move it, not for the developer.
    val orphan = (n: Json) => n("parent").flatMap(_.str).flatMap(ids.get).exists(p => s(p, "state") == "rejected")
    val dev = ns.filter(n => Set("proposed", "review")(s(n, "state")) && !orphan(n)).map { n =>
      val cs = n("causes").map(_.arr.flatMap(_.str)).getOrElse(Nil)
      s"${s(n, "id")}: ${if cs.isEmpty then "proposed" else s"review (${cs.mkString(", ")})"}${if n("mechanical").contains(JBool(true)) then ", mechanical" else ""}"
    } ++
      annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => s"${s(g, "id")}: gone from the model; accept that it is gone" +
        g("renamedTo").map(_.arr.flatMap(_.str)).filter(_.nonEmpty).fold("")(rs => s", or that it was renamed to ${rs.mkString(" or ")} (it says the same)"))
    val revisits = ns.filter(n => n("causes").exists(_.arr.flatMap(_.str).contains("revisit"))).map { n =>
      val why = n("history").map(_.arr.toList).getOrElse(Nil).reverse.find(h => s(h, "action") == "revisit").fold("")(h => s(h, "reason"))
      s"${s(n, "id")}: the developer asked to revisit it ($why): propose a change, or answer on the node (answer with node) why it still holds"
    }
    val agent = ns.filter(n => s(n, "state") == "rejected").map(n => s"${s(n, "id")}: rejected; remove it from the Scala model") ++ revisits ++
      ns.filter(orphan).map(n => s"${s(n, "id")}: rests on rejected ${s(n, "parent")}; move it under the node chosen instead")
    (dev, agent)

  /** The CI gate: every node accepted by the developer, every link proven, every example passing; rejected nodes
    * must be removed from the model, so that nothing still rests on them or is governed by them.
    */
  def complete(annotated: Json): Boolean =
    annotated("gone").forall(_.arr.isEmpty) && nodes(annotated).forall(n => s(n, "state") == "accepted" && unproven(n).isEmpty)

  /** What of a node is not proven (or decided by reading) or fails: the one list the browser and `status` use. */
  def unproven(n: Json): List[String] =
    def bad(k: String, ok: Set[String]) = n(k).map(_.arr.toList).getOrElse(Nil).filterNot(x => ok(s(x, "status")))
    val fine = Set("proven", "informal")
    val (ok, total) = examples(n)
    n("link").filter(l => l != JNull && !fine(s(l, "status"))).map(l => s"its link is ${s(l, "status")}").toList ++
      Option.when(ok != total)(s"${total - ok} example(s) fail") ++
      bad("invariants", fine + "exempt").map(i => s"invariant ${s(i, "id")} is ${s(i, "status")}") ++
      n("implementationProof").filter(p => p != JNull && !fine(s(p, "status"))).map(p => s"its implementation ${s(p, "name")} is ${s(p, "status")}: not proven to meet the contract") ++
      bad("expectations", fine).map(e => s"an expectation is ${s(e, "status")}") ++
      bad("reliances", fine).map(r => s"the guarantee it relies on from ${s(r, "id")} is ${s(r, "status")}")

