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
  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")
  private def nodes(snapshot: Json): List[Json] = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
  private def byId(snapshot: Json): Map[String, Json] = nodes(snapshot).map(n => s(n, "id") -> n).toMap
  private def parentChain(snapshot: Json, n: Json): String =
    val ids = byId(snapshot)
    above(n("parent").flatMap(_.str).flatMap(ids.get).fold("")(s(_, "chain")),
      kept(n).flatMap(ids.get).map(s(_, "chain")))

  /** What a node rests on: its parent's chain, with the chains of the invariants it keeps. */
  def above(parentChain: String, invariantChains: List[String]): String =
    if invariantChains.isEmpty then parentChain else sha((parentChain :: invariantChains.sorted)*)

  private def kept(n: Json): List[String] = n("invariants").map(_.arr.toList).getOrElse(Nil).flatMap(_("id").flatMap(_.str))
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
    val parts = Set("parent", "statement", "sources", "substitutions", "vocabulary", "uses", "governs", "formal")
    Decision.hash(JObj(content.obj.filter(f => parts(f._1))))

  /** IDEA.md split into the idea a root is decided against, and its `## Not modelled` section. */
  def splitIdea(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    val i = lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled"))
    if i < 0 then (idea.trim, "")
    else
      val (section, rest) = lines.drop(i + 1).span(l => !l.startsWith("#"))
      ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)

  /** What moved under a node's decision. A node whose parent was rejected is reviewed as if its
    * parent's meaning moved: what it rests on is no longer chosen.
    */
  def causes(snapshot: Json, ledger: Ledger, n: Json): List[String] =
    val id = s(n, "id")
    val revisit = ledger.current(id).exists(_.action == "revisit")
    val parentRejected = n("parent").flatMap(_.str).flatMap(byId(snapshot).get).exists(p => state(snapshot, ledger, p) == "rejected")
    ledger.binding(id).fold(Nil) { d =>
      List("self" -> (d.hash != s(n, "hash")), "above" -> (d.chain != parentChain(snapshot, n) || parentRejected),
        "code" -> (d.code != code(n)), "revisit" -> revisit, "merged" -> ledger.forked(id)).collect { case (c, true) => c }
    }

  def state(snapshot: Json, ledger: Ledger, n: Json): String =
    ledger.current(s(n, "id")) match
      case Some(d) if d.action == "reject" => if d.hash == s(n, "hash") then "rejected" else "proposed"
      case Some(d) if Ledger.binds(d.action) || d.action == "revisit" =>
        if causes(snapshot, ledger, n).isEmpty then "accepted" else "review"
      case _ => "proposed"

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
        "settledByAgent" -> ledger.settledByAgent(id).fold(JNull)(decisionJson(id, _)),
        "settleable" -> JBool(settleable(snapshot, ledger, n).isEmpty),
        "below" -> JArr(if state(snapshot, ledger, n) == "accepted" && ledger.settledByAgent(id).isEmpty then Nil else below(snapshot, ledger, n)),
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
      (up(n) ++ kept(n).flatMap(ids.get)).flatMap { a =>
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
      revisit: List[String] = Nil, confirm: List[String] = Nil, action: String = "accept", seen: String = "")

  /** Why the agent may not settle `n`, or None if it may. The developer decides every choice: roots,
    * design decisions, a node with alternatives beside it, a node that introduces terms, any change
    * to what a node says. The agent may settle what is left: a mechanical node (or a change to the
    * code it governs) whose link holds and whose examples pass.
    */
  def settleable(snapshot: Json, ledger: Ledger, n: Json): Option[String] =
    val id = s(n, "id")
    val st = state(snapshot, ledger, n)
    val siblings = nodes(snapshot).filter(m => s(m, "id") != id && m("parent") == n("parent") && state(snapshot, ledger, m) != "rejected")
    val introduces = n("content").flatMap(_("vocabulary")).exists(_.arr.nonEmpty)
    val link = n("link").filter(_ != JNull).map(s(_, "status"))
    val (ok, total) = examples(n)
    val codeOnly = st == "review" && causes(snapshot, ledger, n) == List("code")
    // A change inside the code a node governs (a contract's implementation, a component's files) is
    // the agent's to settle; what any node says, and the choice of roots, components and invariants,
    // is the developer's.
    if !codeOnly && !Set("refine", "instantiate", "contract")(s(n, "kind")) then Some(s"${s(n, "kind")} nodes are the developer's to decide")
    else if st == "accepted" then Some(s"$id is already settled")
    else if st == "rejected" then Some(s"$id was rejected")
    else if st == "review" && causes(snapshot, ledger, n) != List("code") then Some(s"what $id says changed: the developer decides")
    else if st == "proposed" && siblings.nonEmpty then Some(s"$id has alternatives beside it: the developer chooses")
    else if st == "proposed" && introduces then Some(s"$id introduces terms: the developer decides what they mean")
    else if waitsFor(snapshot, ledger, n).isDefined then Some(s"$id waits for ${waitsFor(snapshot, ledger, n).get}")
    else if !link.forall(Set("proven", "informal")) then Some(s"$id's link is ${link.getOrElse("unchecked")}")
    else if ok != total then Some(s"${total - ok} of $id's examples fail")
    else None

  /** The decisions below `n` that accepting it can act on, with their reasons, parents first: those
    * accepted (each may be revisited), and those under review only because `n`'s meaning moved
    * (each still holds, or is revisited). Below a node that is under review for anything else,
    * nothing is listed: that node is decided on its own first.
    */
  def below(snapshot: Json, ledger: Ledger, n: Json): List[Json] =
    val id = s(n, "id")
    def children(x: String) = nodes(snapshot).filter(_("parent").flatMap(_.str).contains(x))
    def movedOnlyBy(c: Json) = causes(snapshot, ledger, c) == List("above") &&
      moved(snapshot, ledger, c).flatMap(_("id").flatMap(_.str)).forall(_ == id)
    def go(x: String): List[Json] = children(x).flatMap { c =>
      val cid = s(c, "id")
      val st = state(snapshot, ledger, c)
      val kind = if st == "accepted" && ledger.binding(cid).isDefined then Some("accepted")
        else if st == "review" && movedOnlyBy(c) then Some("moved") else None
      kind.toList.flatMap { k =>
        obj("id" -> str(cid), "kind" -> str(k), "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")),
          "reason" -> str(ledger.chosen(cid).fold("")(_.reason))) :: go(cid)
      }
    }
    val own = go(id)
    // The idea is what every decision rests on: a root's change lists the decisions outside its tree too.
    val elsewhere =
      if s(n, "kind") != "root" then Nil
      else nodes(snapshot).filter { c =>
        val cid = s(c, "id")
        cid != id && !own.exists(b => s(b, "id") == cid) && !isBelow(snapshot, cid, id) &&
          state(snapshot, ledger, c) == "accepted" && ledger.binding(cid).isDefined
      }.map(c => obj("id" -> str(s(c, "id")), "kind" -> str("accepted"),
        "statement" -> c("content").flatMap(_("statement")).getOrElse(str("")), "reason" -> str(ledger.chosen(s(c, "id")).fold("")(_.reason))))
    own ++ elsewhere

  private def isBelow(snapshot: Json, id: String, ancestor: String): Boolean =
    byId(snapshot).get(id).flatMap(_("parent").flatMap(_.str)).exists(p => p == ancestor || isBelow(snapshot, p, ancestor))

  /** The node a decision on `n` waits for: its parent, when `n` rests on it (a proposal, or a node
    * whose parent moved) and the parent is not accepted.
    */
  def waitsFor(snapshot: Json, ledger: Ledger, n: Json): Option[String] =
    val restsOnParent = state(snapshot, ledger, n) == "proposed" || causes(snapshot, ledger, n).contains("above")
    n("parent").flatMap(_.str).filter { p =>
      val ps = byId(snapshot).get(p).map(state(snapshot, ledger, _))
      // Nothing is decided under a parent that is not chosen; what rests on a moved parent waits for it.
      ps.exists(Set("proposed", "rejected")) || (restsOnParent && ps.exists(_ != "accepted"))
    }.orElse(
      // A contract rests on the invariants it keeps, as on its parent.
      if !restsOnParent then None else kept(n).find(i => byId(snapshot).get(i).exists(state(snapshot, ledger, _) != "accepted")))

  /** Applies a decision; the new ledger, or why it is refused. */
  def decide(snapshot: Json, ledger: Ledger, r: Request, at: String, commit: String = "", tree: String = ""): Either[String, Ledger] =
    val ids = byId(snapshot)
    def st(l: Ledger, id: String) = state(snapshot, l, ids(id))
    def make(action: String, n: Json, rejected: List[String], reason: String) =
      Decision(action, n("content").getOrElse(JNull), parentChain(snapshot, n), r.by, at, reason, rejected, code(n), commit, tree)
    if r.by.trim.isEmpty then Left("say who decides")
    else if !Set("accept", "reject", "settle", "acknowledge")(r.action) then Left(s"unknown decision ${r.action}")
    else if r.reason.trim.split("\\s+").count(_.exists(_.isLetter)) < 3 then
      Left("give the reason for the decision in a few words: it is kept as part of the theory")
    else if r.action == "acknowledge" then
      // The developer looked at a restart of the ledger (`seen` is its commit) and says why it is right.
      if r.node != Ledger.Self || r.seen.isEmpty then Left("acknowledge names the ledger and the restart commit")
      else Right(ledger.add(Ledger.Self, Decision("acknowledge", JNull, "", r.by, at, r.reason, commit = r.seen)))
    else if ids.get(r.node).exists(n => r.seen.nonEmpty && r.seen != version(snapshot, n)) then
      Left(s"${r.node} changed since you looked at it: look again before deciding")
    else if !ids.contains(r.node) then
      ledger.current(r.node) match
        case Some(last) if ledger.binding(r.node).isDefined =>
          Right(ledger.add(r.node, last.copy(action = "remove", by = r.by, at = at, reason = r.reason, rejected = Nil, commit = commit, tree = tree)))
        case _ => Left(s"unknown node ${r.node}")
    else
      val n = ids(r.node)
      val parent = n("parent").flatMap(_.str)
      val bad = r.reject.filter(x => x == r.node || !ids.get(x).exists(_("parent").flatMap(_.str) == parent))
      if r.action == "settle" then
        settleable(snapshot, ledger, n) match
          case Some(why) => Left(s"the agent may not settle this: $why")
          case None => Right(ledger.add(r.node, make("settle", n, Nil, r.reason)))
      else if r.action == "reject" then
        if st(ledger, r.node) != "proposed" then Left(s"${r.node} is ${st(ledger, r.node)}: only a proposal is rejected on its own")
        else Right(ledger.add(r.node, make("reject", n, Nil, r.reason)))
      else if waitsFor(snapshot, ledger, n).isDefined then
        Left(s"accept ${parent.get} first: what rests on it is decided after it")
      else if bad.nonEmpty then Left(s"not an alternative to ${r.node}: ${bad.mkString(", ")}")
      else if st(ledger, r.node) == "accepted" && r.reject.isEmpty && r.confirm.isEmpty && r.revisit.isEmpty &&
          ledger.settledByAgent(r.node).isEmpty then Left(s"${r.node} is already accepted")
      else
        // Choosing (or accepting a change to the node itself) is an acceptance; otherwise a confirmation.
        val cs = causes(snapshot, ledger, n)
        val action = if st(ledger, r.node) == "review" && !cs.contains("self") && r.reject.isEmpty then "confirm" else "accept"
        // Accepting what the agent settled endorses it.
        val endorse = st(ledger, r.node) == "accepted" && ledger.settledByAgent(r.node).isDefined
        val chosen = if st(ledger, r.node) == "accepted" && r.reject.isEmpty && !endorse then ledger
          else ledger.add(r.node, make(action, n, r.reject, r.reason))
        val withRejected = r.reject.foldLeft(chosen)((l, x) => l.add(x, make("reject", ids(x), Nil, s"${r.node} was chosen instead: ${r.reason}")))
        def descendants(id: String): List[String] =
          nodes(snapshot).filter(_("parent").flatMap(_.str).contains(id)).flatMap(c => s(c, "id") :: descendants(s(c, "id")))
        val under = descendants(r.node)
        val listed = below(snapshot, ledger, n).map(b => s(b, "id") -> s(b, "kind")).toMap
        val notListed = r.revisit.filterNot(listed.contains) ++ r.confirm.filterNot(x => listed.get(x).contains("moved"))
        if notListed.nonEmpty then Left(s"not among the decisions below ${r.node} that this decision can act on: ${notListed.mkString(", ")}")
        else if r.revisit.exists(r.confirm.contains) then Left("a node is either revisited or confirmed")
        else
          // Parents first: a node named to confirm is confirmed once its parent is accepted, and only
          // if it is under review just because something above it moved.
          val confirmed = under.filter(r.confirm.contains).foldLeft(withRejected) { (l, id) =>
            val c = ids(id)
            val parentAccepted = c("parent").flatMap(_.str).forall(p => st(l, p) == "accepted")
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
        else if s(n, "state") == "rejected" then "rejected: remove it from the model" else s(n, "state")
      val link = n("link").filter(_ != JNull).fold("") { l => s", link ${s(l, "status")}${if s(l, "detail").nonEmpty then s" (${s(l, "detail")})" else ""}" }
      val (ok, total) = examples(n)
      val ex = if total == 0 then "" else s", examples $ok/$total"
      val inv = n("invariants").map(_.arr.toList).getOrElse(Nil).map(i => s"${s(i, "id")} ${s(i, "status")}")
      val keeps = if inv.isEmpty then "" else s", keeps ${inv.mkString(", ")}"
      val covers = n("covers").map(_.arr.flatMap(_.str).toList).filter(_.nonEmpty).fold("")(cs => s", kept by ${cs.mkString(", ")}")
      val here = if mark.contains(s(n, "id")) then "   ← this node" else ""
      s"${"  " * depth}${s(n, "id")} (${s(n, "kind")})  [$st$link$ex$keeps$covers]$here" ::
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
    else
      val words = query.toLowerCase.split("\\W+").filter(_.length > 2).toList
      def text(n: Json) = (s(n, "id") :: List("statement", "why").flatMap(k => n("content").flatMap(_(k)).flatMap(_.str)) ++
        n("decision").filter(_ != JNull).flatMap(_("reason")).flatMap(_.str).toList).mkString(" ").toLowerCase
      val hits = ns.map(n => n -> words.count(text(n).contains)).filter(_._2 > 0).sortBy(-_._2).take(10).map(_._1)
      if hits.isEmpty then s"No node governs or mentions \"$query\": a new concern may need a new node (and a governed home for its code)."
      else ("Nodes that mention it, best first:" :: hits.map(line)).mkString("\n")

  /** What waits on whom: decisions for the developer, clean-up for the agent. */
  def waiting(annotated: Json): (List[String], List[String]) =
    val ns = nodes(annotated)
    val ids = byId(annotated)
    // A node resting on a rejected node waits for the agent to move it, not for the developer.
    val orphan = (n: Json) => n("parent").flatMap(_.str).flatMap(ids.get).exists(p => s(p, "state") == "rejected")
    val agentMay = (n: Json) => n("settleable").contains(JBool(true))
    val dev = ns.filter(n => Set("proposed", "review")(s(n, "state")) && !orphan(n) && !agentMay(n)).map { n =>
      val cs = n("causes").map(_.arr.flatMap(_.str)).getOrElse(Nil)
      s"${s(n, "id")}: ${if cs.isEmpty then "proposed" else s"review (${cs.mkString(", ")})"}"
    } ++ annotated("gone").map(_.arr.toList).getOrElse(Nil).map(g => s"${s(g, "id")}: gone from the model; accept that it is gone")
    val agent = ns.filter(n => s(n, "state") == "rejected").map(n => s"${s(n, "id")}: rejected; remove it from the Scala model") ++
      ns.filter(orphan).map(n => s"${s(n, "id")}: rests on rejected ${s(n, "parent")}; move it under the node chosen instead") ++
      ns.filter(agentMay).map(n => s"${s(n, "id")}: mechanical; settle it (settle tool) once you have read its reasons and those around it")
    (dev, agent)

  /** Whether every node is accepted, every link proven, and every example passing; rejected nodes
    * must be removed from the model, so that nothing still rests on them or is governed by them.
    */
  def settled(annotated: Json): Boolean =
    val ns = nodes(annotated)
    annotated("gone").forall(_.arr.isEmpty) && ns.forall { n =>
      val (ok, total) = examples(n)
      s(n, "state") == "accepted" && n("link").forall(l => l == JNull || Set("proven", "informal")(s(l, "status"))) && ok == total &&
        n("invariants").forall(_.arr.forall(i => Set("proven", "informal")(s(i, "status"))))
    }
