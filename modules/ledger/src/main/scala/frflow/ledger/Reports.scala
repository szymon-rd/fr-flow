package frflow
package ledger

import frflow.protocol.*

/** What the developer and the agent read of an annotated snapshot: the tree, what waits for whom, where
  * a change belongs, and whether everything is decided and proven. The same for every reader.
  */
object Reports:

  /** Running code as named in a summary: `LoanIndex(...).borrow` as `LoanIndex.borrow`. */
  def runningCode(wiring: String): String =
    val body = wiring.trim.replaceFirst("""^\([^()]*\)\s*=>\s*|^\w+\s*=>\s*""", "")
    val flat = StringBuilder()
    var depth = 0
    body.foreach(c => if c == '(' then depth += 1 else if c == ')' then depth -= 1 else if depth == 0 then flat += c)
    val name = flat.result().replace(".value", "").replaceAll("\\s+", " ").trim
    if name.nonEmpty && name.length <= 60 then name else body.take(57) + "…"

  /** How a contract's code is proven, in the words every summary uses: "proven down to its code"
    * (a proven define, any running code checked against it), or "checked by running".
    */
  private def codeOf(n: SnapNode): String =
    val impl = n.content.text("implementation")
    val runs = impl.linesIterator.find(_.startsWith("runs: ")).map(r => s"; running code ${runningCode(r.stripPrefix("runs: "))} checked against it").getOrElse("")
    n.implementationProof match
      case Some(p) if p.status == ObligationStatus.Proven => s", proven down to its code (define ${p.name}$runs)"
      case Some(p) => s", define ${p.name} ${p.status}$runs"
      case None if impl.nonEmpty => ", code checked by running"
      case None => ""

  /** The tree as text, from the root: each node under its first parent (and "also under" the others),
    * with its state (and what moved), how its parts make it, its examples; then the definitions, and
    * the nodes under no parent besides the root.
    */
  def tree(annotated: Annotated): String =
    val ns = annotated.nodes
    val ids = ns.map(_.id).toSet
    def go(r: Reviewed, depth: Int): List[String] =
      val n = r.node
      val cs = r.review.causes
      val st = if cs.nonEmpty then s"review: ${cs.mkString(", ")}"
        else if r.state == ReviewState.Rejected then "rejected: remove it from the model"
        else r.state.toString
      val split = n.split.fold("") { sp =>
        val c = sp.complete
        val notNeeded = sp.needed.filter(_.status == ObligationStatus.NotNeeded).map(_.id)
        s", parts ${c.status}${if c.detail.nonEmpty then s" (${c.detail})" else ""}" +
          (if notNeeded.nonEmpty then s", not needed: ${notNeeded.mkString(", ")}" else "") +
          (if sp.clash.status == ObligationStatus.Clash then ", parts clash" else "")
      }
      val check = n.status.filter(x => x != CheckStatus.Proven && x != CheckStatus.Informal).fold("")(x => s", $x")
      val (ok, total) = n.examplesPassing
      val ex = if total == 0 then "" else s", examples $ok/$total"
      val (exempt, kept) = n.invariants.partition(_.status == ObligationStatus.Exempt)
      val keeps = (if kept.isEmpty then "" else s", keeps ${kept.map(i => s"${i.id} ${i.status}").mkString(", ")}") +
        (if exempt.isEmpty then "" else s", exempt from ${exempt.map(_.id).mkString(", ")}")
      val exps = n.expectations.filter(_.status != ObligationStatus.Informal)
      val notProven = exps.filter(_.status != ObligationStatus.Proven)
      def short(t: String) = if t.length > 80 then t.take(79) + "…" else t
      val expects = if exps.isEmpty then "" else if notProven.isEmpty then s", expectations ${exps.size}/${exps.size} proven"
        else s", expectations ${exps.size - notProven.size}/${exps.size} proven (${notProven.map(e => s"${e.status}: \"${short(e.statement)}\"").mkString("; ")})"
      val also = n.parents.filter(ids).drop(1)
      s"${"  " * depth}${n.id} (${n.shownKind})  [$st$check$split$ex$expects$keeps${codeOf(n)}]${if also.isEmpty then "" else s" (also under ${also.mkString(", ")})"}" ::
        ns.filter(c => c.node.parents.filter(ids).headOption.contains(n.id)).flatMap(go(_, depth + 1))
    val gone = annotated.gone.map(g => s"${g.id}  [review: gone]")
    val tops = ns.filter(_.node.parents.forall(p => !ids(p)))
    val (defs, others) = tops.filterNot(_.node.isRoot).partition(_.node.kind == NodeKind.Definition)
    (tops.filter(_.node.isRoot).flatMap(go(_, 0)) ++ others.flatMap(go(_, 0)) ++
      (if defs.isEmpty then Nil else "Definitions:" :: defs.flatMap(go(_, 1))) ++ gone).mkString("\n")

  /** Where a change belongs: the nodes governing a file, or what mentions every word asked for (their
    * id, statement or reasons, the options rejected, the idea).
    */
  def find(annotated: Annotated, query: String): String =
    val ns = annotated.nodes
    def files(r: Reviewed) = r.node.code.fold(Nil)(_.files)
    def line(r: Reviewed) = s"- ${r.id} (${r.node.shownKind}, ${r.state}): ${r.node.content.statement}"
    val q = query.stripPrefix("./")
    val governing = ns.filter(r => files(r).exists(f => f == q || f.startsWith(q.stripSuffix("/") + "/") || q.startsWith(f.stripSuffix("/") + "/")))
    if governing.nonEmpty then ("Governed by:" :: governing.map(line)).mkString("\n")
    else if q.contains('/') || q.endsWith(".scala") then
      s"No node governs $q: code there changes unnoticed (status fails on it). Give it a home: the contract whose implementation it is, or a design node."
    else
      // Everything the theory says, as entries: the nodes (with their reasons), the options rejected
      // (gone from the model or not), the gone nodes, and the lines of what is not modelled.
      final case class Entry(label: String, text: String)
      def content(k: String) = ns.flatMap(_.node.content.str(k)).distinct
      val nodeEntries = ns.map(r => Entry(line(r), (r.id.value :: List("statement", "why").flatMap(r.node.content.str) ++
        r.review.history.map(_.reason)).mkString(" \n")))
      val rejected = ns.flatMap(_.review.rejectedBeside).distinctBy(_.id).filterNot(r => ns.exists(_.id == r.id))
        .map(r => Entry(s"- rejected ${r.id}: ${r.statement} — rejected because: ${r.reason}", s"${r.id} ${r.statement} \n${r.why} \n${r.reason}"))
      val gone = annotated.gone.map(g => Entry(s"- gone ${g.id}", s"${g.id} ${g.decision.reason}"))
      val notModelled = content("notModelled").flatMap(_.split("\n(?=- )").map(_.trim).filter(_.nonEmpty)).distinct
        .map(l => Entry(s"- not modelled: ${l.replaceAll("\\s+", " ")}", l))
      // The idea's lines and the terms' meanings say what the model is about too.
      val ideaLines = content("idea").flatMap(_.split("\n\\s*\n").map(_.trim).filter(l => l.nonEmpty && !l.startsWith("#"))).distinct
        .map(l => Entry(s"- idea: ${l.replaceAll("\\s+", " ").take(160)}", l))
      val terms = ns.flatMap(r => r.node.content.strs("vocabulary").map(r.id -> _)).distinctBy(_._2).map((id, v) => Entry(s"- term (at $id): $v", v))
      val all = nodeEntries ++ rejected ++ gone ++ notModelled ++ ideaLines ++ terms
      // Every word of the query, anywhere in the entry, whatever the case.
      val words = query.toLowerCase.split("\\s+").filter(_.nonEmpty).toList
      val found = all.filter(e => words.forall(e.text.toLowerCase.contains)).take(10)
      def sentence(e: Entry) = e.text.split("(?<=[.!?])\\s+|\n").find(x => words.exists(x.toLowerCase.contains)).map(_.trim).filter(_.nonEmpty)
      if found.isEmpty then s"No node, rejected option or not-modelled line mentions \"$query\": a new concern may need a new node (and a governed home for its code)."
      else ("What mentions it:" :: found.map(e => e.label + sentence(e).filterNot(e.label.contains).fold("")(x => s"\n    \"${x.take(200)}\""))).mkString("\n")

  /** What the agent starts from: the developer's open requests, warnings, what is the agent's to do,
    * what waits for the developer, and the tree. The same for every reader.
    */
  def inbox(annotated: Option[Annotated], requests: List[Request]): String =
    val open = requests.filter(_.status == RequestStatus.Open)
    val reqs =
      if open.isEmpty then List("No open requests.")
      else "Open requests from the developer:" :: open.map(r =>
        s"- [${r.id}] on ${r.node.map(_.value).filter(_.nonEmpty).getOrElse("(the idea)")}: ${r.text}")
    val rest = annotated.fold(List("", "No snapshot yet; render first.")) { a =>
      val (dev, agent) = waiting(a)
      val warnings = a.snapshot.warnings
      (if warnings.isEmpty then Nil else "" :: "Warnings (status fails on each; fix those in the code):" :: warnings.map("- " + _)) ++
        (if agent.isEmpty then Nil else "" :: "For you:" :: agent.map("- " + _)) ++
        (if dev.isEmpty then Nil else "" :: "Waiting for the developer's decision:" :: dev.map("- " + _))
    }
    (reqs ++ rest).mkString("\n") + annotated.fold("")(a => "\n\nThe tree:\n" + tree(a))

  /** What waits for the developers: how many decisions, how many of them mechanical (one batch) and
    * how many to judge (new nodes, changes). The cost of a change in decisions, seen as it happens.
    */
  def load(annotated: Annotated): String =
    val ns = forDeveloper(annotated)
    val gone = annotated.gone.size
    if ns.isEmpty && gone == 0 then ""
    else
      val mech = ns.count(_.review.mechanical)
      val (fresh, changed) = ns.filterNot(_.review.mechanical).partition(_.state == ReviewState.Proposed)
      s"Decisions waiting: ${ns.size + gone} (${mech} mechanical, decided in one batch; ${fresh.size} new and ${changed.size} changed to judge" +
        (if gone == 0 then ")" else s"; $gone gone from the model)") + ".\n"

  /** The parents of a node that were rejected: it waits for the agent to move it. */
  private def rejectedParents(a: Annotated, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => a.byId.get(p).exists(_.state == ReviewState.Rejected))

  /** The nodes waiting for a developer's decision: proposed or under review, and not resting on a
    * rejected node (that one waits for the agent to move it). `load` and `waiting` count the same.
    */
  private def forDeveloper(a: Annotated): List[Reviewed] =
    a.nodes.filter(r => (r.state == ReviewState.Proposed || r.state == ReviewState.Review) && rejectedParents(a, r).isEmpty)

  /** What waits for the developer, and what is the agent's to do. */
  def waiting(a: Annotated): (List[String], List[String]) =
    def own(r: Reviewed) =
      val cs = r.review.causes
      s"${r.id}: ${if cs.isEmpty then "proposed" else s"review (${cs.mkString(", ")})"}${if r.review.mechanical then ", mechanical" else ""}"
    val dev = forDeveloper(a).map(own) ++ a.gone.map(g => s"${g.id}: gone from the model; accept that it is gone")
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit)).map { r =>
      val why = r.review.history.reverse.find(_.action == Action.Revisit).fold("")(_.reason)
      s"${r.id}: the developer asked to revisit it ($why): propose a change, or answer on the node (answer with node) why it still holds"
    }
    // The developer's reason may ask for something in its place: the agent reads it before removing the node.
    def rejection(r: Reviewed) = r.review.history.reverse.find(_.action == Action.Reject)
      .fold("rejected")(h => s"rejected by ${h.by}: ${h.reason.trim.stripSuffix(".")}")
    val agent = a.nodes.filter(_.state == ReviewState.Rejected)
      .map(r => s"${r.id}: ${rejection(r)}; propose what the reason asks for in its place, or remove it from the Scala model") ++ revisits ++
      a.nodes.filter(rejectedParents(a, _).nonEmpty)
        .map(r => s"${r.id}: rests on rejected ${rejectedParents(a, r).mkString(", ")}; move it under the node chosen instead")
    (dev, agent)

  /** The CI gate: every node accepted by the developer, every node proven, every example passing; rejected nodes
    * must be removed from the model, so that nothing still rests on them or is governed by them.
    */
  def complete(a: Annotated): Boolean =
    a.gone.isEmpty && a.nodes.forall(r => r.state == ReviewState.Accepted && unproven(r.node).isEmpty)

  /** What of a node is not proven (or decided by reading) or fails: the one list `status` uses. */
  def unproven(n: SnapNode): List[String] =
    def fine(s: ObligationStatus) = s == ObligationStatus.Proven || s == ObligationStatus.Informal
    val (ok, total) = n.examplesPassing
    n.status.filterNot(s => s == CheckStatus.Proven || s == CheckStatus.Informal)
      .map(st => s"its check is $st${n.messages.headOption.fold("")(m => s": ${m.linesIterator.nextOption().getOrElse("")}")}").toList ++
      n.split.map(_.complete).filterNot(c => fine(c.status)).map(c => s"its parts are not proven to make it (${c.status}: ${c.detail})") ++
      n.split.toList.flatMap(_.needed).filter(_.status == ObligationStatus.NotNeeded).map(x => s"${x.id} is not needed for it: ${x.detail}") ++
      n.split.map(_.clash).filter(_.status == ObligationStatus.Clash).map(_ => "its parts contradict each other") ++
      Option.when(n.leaf)("nothing below proves it: add the parts that make it, or a contract") ++
      Option.when(ok != total)(s"${total - ok} example(s) fail") ++
      n.invariants.filterNot(i => fine(i.status) || i.status == ObligationStatus.Exempt).map(i => s"invariant ${i.id} is ${i.status}") ++
      n.implementationProof.filterNot(p => fine(p.status)).map(p => s"its implementation ${p.name} is ${p.status}: not proven to meet the contract") ++
      n.rootImpl.filterNot(p => fine(p.status)).map(p => s"root_impl is ${p.status}: the root is not proven of the code") ++
      n.expectations.filterNot(e => fine(e.status)).map(e => s"an expectation is ${e.status}") ++
      // A root doing nothing meets says only what must not happen: the system can drop every feature unnoticed.
      n.idle.map(what => s"Lean shows doing nothing meets it ($what): say what users can do, so the root is stated as exactly")
