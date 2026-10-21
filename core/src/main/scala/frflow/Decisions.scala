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
  *   - `accepted`: decided, and nothing moved since;
  *   - `review`: something moved since it was decided; `causes` say what:
  *     `self` (the node changed), `above` (the meaning of an ancestor changed), `code` (the code
  *     it governs changed), `revisit` (the developer said a change above, such as an edit of the
  *     idea, may affect it); a decided node no longer in the model is listed under `gone`;
  *   - `rejected`: an alternative was chosen instead; the agent removes it from the model.
  *
  * One verb: `accept`. Accepting a proposal chooses it (rejecting alternatives); accepting a node
  * under review says it holds as it now is (recorded as a confirmation when only something above
  * it or its code moved, so the reason it was chosen stays); accepting a gone node agrees that it
  * is gone. When accepting a change, the developer names the decisions below that it may affect
  * (`revisit`): the reasons below are where the conditions for revisiting them are written.
  */
object Decisions:
  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
  private def nodes(snapshot: Json): List[Json] = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
  private def byId(snapshot: Json): Map[String, Json] = nodes(snapshot).map(n => s(n, "id") -> n).toMap
  private def parentChain(snapshot: Json, n: Json): String =
    n("parent").flatMap(_.str).flatMap(byId(snapshot).get).fold("")(s(_, "chain"))
  private def code(n: Json): String = n("code").flatMap(_("fingerprint")).flatMap(_.str).getOrElse("")
  private def sha(parts: String*): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(parts.mkString("\u0000").getBytes("UTF-8")).map("%02x".format(_)).mkString

  /** A node's chain: what its content means, together with its ancestors'. A change to a node's
    * meaning puts the nodes below up for review; rewording its reason, adding an example, or
    * editing the idea reviews only the node itself.
    */
  def chain(content: Json, parentChain: String): String = sha(meaning(content), parentChain)

  /** What a node's content means, without its reason, examples or idea. */
  def meaning(content: Json): String =
    val parts = Set("parent", "statement", "sources", "substitutions", "vocabulary", "uses", "governs")
    Decision.hash(JObj(content.obj.filter(f => parts(f._1))))

  /** IDEA.md split into the idea a root is decided against, and its `## Not modelled` section. */
  def splitIdea(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    val i = lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled"))
    if i < 0 then (idea.trim, "")
    else
      val (section, rest) = lines.drop(i + 1).span(l => !l.startsWith("#"))
      ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)

  /** The snapshot after an edit of IDEA.md: the roots' content, and every hash and chain, updated
    * without rebuilding the model (the idea is the only input that changed).
    */
  def withIdea(snapshot: Json, idea: String): Json =
    val (decided, notModelled) = splitIdea(idea)
    val ns = nodes(snapshot)
    val updated = scala.collection.mutable.Map.empty[String, Json]
    def put(k: String, v: Json)(j: Json) = JObj(j.obj.filterNot(_._1 == k) :+ (k -> v))
    def visit(n: Json, pc: String): Unit =
      val content0 = n("content").getOrElse(obj())
      val content = if s(n, "kind") == "root" then put("notModelled", str(notModelled))(put("idea", str(decided))(content0)) else content0
      val ch = chain(content, pc)
      updated(s(n, "id")) = put("chain", str(ch))(put("hash", str(Decision.hash(content)))(put("content", content)(n)))
      ns.filter(_("parent").flatMap(_.str).contains(s(n, "id"))).foreach(visit(_, ch))
    ns.filter(_("parent").forall(_ == JNull)).foreach(visit(_, ""))
    put("idea", str(idea))(put("nodes", JArr(ns.map(n => updated.getOrElse(s(n, "id"), n))))(snapshot))

  /** What moved under a node's decision. */
  def causes(ledger: Ledger, n: Json, parentChain: String): List[String] =
    val id = s(n, "id")
    val revisit = ledger.current(id).exists(_.action == "revisit")
    ledger.binding(id).fold(Nil) { d =>
        List("self" -> (d.hash != s(n, "hash")), "above" -> (d.chain != parentChain), "code" -> (d.code != code(n)),
          "revisit" -> revisit).collect { case (c, true) => c }
      }

  def state(ledger: Ledger, n: Json, parentChain: String): String =
    ledger.current(s(n, "id")) match
      case Some(d) if d.action == "reject" => if d.hash == s(n, "hash") then "rejected" else "proposed"
      case Some(d) if d.action == "accept" || d.action == "confirm" || d.action == "revisit" =>
        if causes(ledger, n, parentChain).isEmpty then "accepted" else "review"
      case _ => "proposed"

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
      val pc = parentChain(snapshot, n)
      val fields = Seq(
        "state" -> str(state(ledger, n, pc)),
        "causes" -> JArr(causes(ledger, n, pc).map(str)),
        "moved" -> JArr(moved(snapshot, ledger, n)),
        "decision" -> ledger.chosen(id).fold(JNull)(decisionJson(id, _)),
        "history" -> JArr(ledger.history(id).map(decisionJson(id, _))),
        "alternatives" -> JArr(ledger.alternatives(id).map((a, c) => obj("id" -> str(a), "content" -> c))))
      JObj(n.obj.filterNot(f => fields.exists(_._1 == f._1)) ++ fields)
    }
    val gone = ledger.decisions.toList.sortBy(_._1).collect {
      case (id, ds) if !ids.contains(id) && ledger.binding(id).isDefined =>
        obj("id" -> str(id), "decision" -> decisionJson(id, ds.last))
    }
    JObj(snapshot.obj.filterNot(f => f._1 == "nodes" || f._1 == "gone") ++ Seq("nodes" -> JArr(annotated), "gone" -> JArr(gone)))

  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its
    * content as it was then: what the browser shows for the cause `above`.
    */
  private def moved(snapshot: Json, ledger: Ledger, n: Json): List[Json] =
    ledger.binding(s(n, "id")).filter(_.chain != parentChain(snapshot, n)).fold(Nil) { d =>
      val ids = byId(snapshot)
      def up(x: Json): List[Json] = x("parent").flatMap(_.str).flatMap(ids.get).fold(Nil)(p => p :: up(p))
      up(n).flatMap { a =>
        val id = s(a, "id")
        val then_ = ledger.history(id).filter(x => (x.action == "accept" || x.action == "confirm") && x.at <= d.at).lastOption
        val now = a("content").getOrElse(JNull)
        then_.filter(t => meaning(t.content) != meaning(now)).map(t => obj("id" -> str(id), "before" -> t.content))
      }
    }

  /** Every decision, newest first: the history of the theory. */
  def history(ledger: Ledger): Json = JArr(ledger.all.map(decisionJson(_, _)))

  /** A decision: `accept` the node, rejecting the given alternatives (or, when `reject` names only
    * the node itself, reject it); with `subtree`, also every
    * node below it that is under review only because something above it moved.
    */
  final case class Request(node: String, by: String, reason: String, reject: List[String] = Nil, subtree: Boolean = false,
      revisit: List[String] = Nil)

  /** Applies a decision; the new ledger, or why it is refused. */
  def decide(snapshot: Json, ledger: Ledger, r: Request, at: String, commit: String = ""): Either[String, Ledger] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: String) = state(l, ids(id), parentChain(snapshot, ids(id)))
    def make(action: String, n: Json, rejected: List[String], reason: String) =
      Decision(action, n("content").getOrElse(JNull), parentChain(snapshot, n), r.by, at, reason, rejected, code(n), commit)
    if r.by.trim.isEmpty then Left("say who decides")
    else if r.reason.trim.split("\\s+").count(_.exists(_.isLetter)) < 3 then
      Left("give the reason for the decision in a few words: it is kept as part of the theory")
    else if !ids.contains(r.node) then
      ledger.current(r.node) match
        case Some(last) if ledger.binding(r.node).isDefined =>
          Right(ledger.add(r.node, last.copy(action = "remove", by = r.by, at = at, reason = r.reason, rejected = Nil, commit = commit)))
        case _ => Left(s"unknown node ${r.node}")
    else
      val n = ids(r.node)
      val parent = n("parent").flatMap(_.str)
      val bad = r.reject.filter(x => x == r.node || !ids.get(x).exists(_("parent").flatMap(_.str) == parent))
      // Rejecting a proposal on its own: no alternative is chosen.
      if r.reject == List(r.node) then
        if st(ledger, r.node) != "proposed" then Left(s"${r.node} is ${st(ledger, r.node)}: only a proposal is rejected on its own")
        else Right(ledger.add(r.node, make("reject", n, Nil, r.reason)))
      else if parent.exists(p => st(ledger, p) != "accepted") then Left(s"accept ${parent.get} first: the tree is decided from the root down")
      else if bad.nonEmpty then Left(s"not an alternative to ${r.node}: ${bad.mkString(", ")}")
      else if st(ledger, r.node) == "accepted" && r.reject.isEmpty && !r.subtree && r.revisit.isEmpty then Left(s"${r.node} is already accepted")
      else
        // Choosing (or accepting a change to the node itself) is an acceptance; otherwise a confirmation.
        val cs = causes(ledger, n, parentChain(snapshot, n))
        val action = if st(ledger, r.node) == "review" && !cs.contains("self") && r.reject.isEmpty then "confirm" else "accept"
        val chosen = if st(ledger, r.node) == "accepted" && r.reject.isEmpty then ledger else ledger.add(r.node, make(action, n, r.reject, r.reason))
        val withRejected = r.reject.foldLeft(chosen)((l, x) => l.add(x, make("reject", ids(x), Nil, s"${r.node} was chosen instead: ${r.reason}")))
        // Below the node, parents first: confirm what is under review only because something above
        // moved, and only once its own parent is accepted.
        def below(id: String): List[String] =
          nodes(snapshot).filter(_("parent").flatMap(_.str).contains(id)).flatMap(c => s(c, "id") :: below(s(c, "id")))
        val under = below(r.node)
        val confirmed = if !r.subtree then withRejected else under.foldLeft(withRejected) { (l, id) =>
          val c = ids(id)
          val parentAccepted = c("parent").flatMap(_.str).forall(p => st(l, p) == "accepted")
          if parentAccepted && st(l, id) == "review" && causes(l, c, parentChain(snapshot, c)) == List("above") then
            l.add(id, make("confirm", c, Nil, s"still holds after ${r.node} changed: ${r.reason}"))
          else l
        }
        // Decisions below that the developer says this change affects go back to review.
        val notBelow = r.revisit.filterNot(x => under.contains(x) && confirmed.binding(x).isDefined)
        if notBelow.nonEmpty then Left(s"only decided nodes below ${r.node} can be revisited: ${notBelow.mkString(", ")}")
        else Right(r.revisit.distinct.foldLeft(confirmed)((l, id) =>
          l.add(id, make("revisit", ids(id), Nil, s"${r.node} changed and may affect it: ${r.reason}"))))

  // -- views: the same for the CLI, the browser and the agent ---------------------------------

  private def examples(n: Json): (Int, Int) =
    val ex = n("examples").map(_.arr.toList).getOrElse(Nil)
    (ex.count(e => s(e, "contract") == "ok" && e("implementation").forall(i => i == JNull || i.str.contains("ok"))), ex.size)

  /** The tree as text: each node's state (and what moved), its link to the parent, its examples. */
  def tree(annotated: Json, mark: Option[String] = None): String =
    val ns = nodes(annotated).filterNot(n => s(n, "state") == "rejected")
    def go(n: Json, depth: Int): List[String] =
      val cs = n("causes").map(_.arr.flatMap(_.str)).getOrElse(Nil)
      val st = if cs.isEmpty then s(n, "state") else s"review: ${cs.mkString(", ")}"
      val link = n("link").filter(_ != JNull).fold("") { l => s", link ${s(l, "status")}${if s(l, "detail").nonEmpty then s" (${s(l, "detail")})" else ""}" }
      val (ok, total) = examples(n)
      val ex = if total == 0 then "" else s", examples $ok/$total"
      val here = if mark.contains(s(n, "id")) then "   ← this node" else ""
      s"${"  " * depth}${s(n, "id")} (${s(n, "kind")})  [$st$link$ex]$here" ::
        ns.filter(_("parent").flatMap(_.str).contains(s(n, "id"))).flatMap(go(_, depth + 1))
    val gone = annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => s"${s(g, "id")}  [review: gone]")
    (ns.filter(_("parent").forall(_ == JNull)).flatMap(go(_, 0)) ++ gone).mkString("\n")

  /** What waits on whom: decisions for the developer, clean-up for the agent. */
  def waiting(annotated: Json): (List[String], List[String]) =
    val ns = nodes(annotated)
    val dev = ns.filter(n => Set("proposed", "review")(s(n, "state"))).map { n =>
      val cs = n("causes").map(_.arr.flatMap(_.str)).getOrElse(Nil)
      s"${s(n, "id")}: ${if cs.isEmpty then "proposed" else s"review (${cs.mkString(", ")})"}"
    } ++ annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => s"${s(g, "id")}: gone from the model; accept that it is gone")
    val agent = ns.filter(n => s(n, "state") == "rejected").map(n => s"${s(n, "id")}: rejected; remove it from the Scala model")
    (dev, agent)

  /** Whether every node is accepted, every link proven, and every example passing. */
  def settled(annotated: Json): Boolean =
    val ns = nodes(annotated).filterNot(n => s(n, "state") == "rejected")
    annotated("gone").forall(_.arr.isEmpty) && ns.forall { n =>
      val (ok, total) = examples(n)
      s(n, "state") == "accepted" && n("link").forall(l => l == JNull || s(l, "status") == "proven") && ok == total
    }
