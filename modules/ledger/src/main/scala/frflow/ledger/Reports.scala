package frflow
package ledger

import frflow.protocol.*

/** The reports as plain text, as today's commands print them (`status`, `inbox`, `find`), rendered from
  * the typed values (`Tree`, `Inbox`, `Found`, `Load`). For agents and CI until the new CLI renders them.
  */
object Reports:

  def complete(a: Annotated): Boolean = Proofs.complete(a)
  def unproven(n: SnapNode): List[String] = Proofs.unproven(n)
  def runningCode(wiring: String): String = Proofs.runningCode(wiring)

  /** The tree as text, from the root: each node under its first parent (and "also under" the others),
    * with its state (and what moved), how its parts make it, its examples; then the definitions, and
    * the nodes under no parent besides the root.
    */
  def tree(a: Annotated): String = treeLines(a, Tree.of(a)).mkString("\n")

  private def treeLines(a: Annotated, t: Tree): List[String] =
    def go(b: Branch, depth: Int): List[String] =
      a.byId.get(b.id).fold(Nil)(r => s"${"  " * depth}${line(r)}${also(b.alsoUnder)}" :: b.children.flatMap(go(_, depth + 1)))
    t.roots.flatMap(go(_, 0)) ++ t.others.flatMap(go(_, 0)) ++
      (if t.definitions.isEmpty then Nil else "Definitions:" :: t.definitions.flatMap(go(_, 1))) ++
      t.gone.map(id => s"$id  [review: gone]")

  private def also(ps: List[NodeId]) = if ps.isEmpty then "" else s" (also under ${ps.mkString(", ")})"

  private def line(r: Reviewed): String =
    val n = r.node
    val cs = r.review.causes
    val st = if cs.nonEmpty then s"review: ${cs.mkString(", ")}"
      else if r.state == ReviewState.Rejected then "rejected: remove it from the model"
      else r.state.toString
    val check = n.status.filter(x => x != CheckStatus.Proven && x != CheckStatus.Informal).fold("")(x => s", $x")
    val (ok, total) = n.examplesPassing
    val examples = if total == 0 then "" else s", examples $ok/$total"
    s"${n.id} (${n.shownKind})  [$st$check${split(n)}$examples${expectations(n)}${keeps(n)}${code(n)}]"

  private def split(n: SnapNode): String = n.split.fold("") { sp =>
    val c = sp.complete
    val notNeeded = sp.needed.filter(_.status == ObligationStatus.NotNeeded).map(_.id)
    s", parts ${c.status}${if c.detail.nonEmpty then s" (${c.detail})" else ""}" +
      (if notNeeded.nonEmpty then s", not needed: ${notNeeded.mkString(", ")}" else "") +
      (if sp.clash.status == ObligationStatus.Clash then ", parts clash" else "")
  }

  private def expectations(n: SnapNode): String =
    val exps = n.expectations.filter(_.status != ObligationStatus.Informal)
    val notProven = exps.filter(_.status != ObligationStatus.Proven)
    def short(t: String) = if t.length > 80 then t.take(79) + "…" else t
    if exps.isEmpty then ""
    else if notProven.isEmpty then s", expectations ${exps.size}/${exps.size} proven"
    else s", expectations ${exps.size - notProven.size}/${exps.size} proven (${notProven.map(e => s"${e.status}: \"${short(e.statement)}\"").mkString("; ")})"

  private def keeps(n: SnapNode): String =
    val (exempt, kept) = n.invariants.partition(_.status == ObligationStatus.Exempt)
    (if kept.isEmpty then "" else s", keeps ${kept.map(i => s"${i.id} ${i.status}").mkString(", ")}") +
      (if exempt.isEmpty then "" else s", exempt from ${exempt.map(_.id).mkString(", ")}")

  /** How a contract's code is proven, in the words every summary uses. */
  private def code(n: SnapNode): String =
    def runs(r: Option[String]) = r.fold("")(c => s"; running code $c checked against it")
    CodeProof.of(n).fold("") {
      case CodeProof.ProvenDown(define, r) => s", proven down to its code (define $define${runs(r)})"
      case CodeProof.Define(name, status, r) => s", define $name $status${runs(r)}"
      case CodeProof.ByRunning => ", code checked by running"
    }

  /** Where a change belongs, as text (see `Find`). */
  def find(a: Annotated, query: String): String = Find(a, query) match
    case Found.Governed(_, ids) => ("Governed by:" :: ids.flatMap(a.byId.get).map(nodeLine)).mkString("\n")
    case Found.Ungoverned(q) =>
      s"No node governs $q: code there changes unnoticed (status fails on it). Give it a home: the contract whose implementation it is, or a design node."
    case Found.Nothing(q) =>
      s"No node, rejected option or not-modelled line mentions \"$q\": a new concern may need a new node (and a governed home for its code)."
    case Found.Mentions(_, ms) =>
      ("What mentions it:" :: ms.map { m =>
        val label = mentionLabel(a, m.what)
        label + m.sentence.filterNot(label.contains).fold("")(x => s"\n    \"${x.take(200)}\"")
      }).mkString("\n")

  private def nodeLine(r: Reviewed) = s"- ${r.id} (${r.node.shownKind}, ${r.state}): ${r.node.content.statement}"
  private def flat(s: String) = s.replaceAll("\\s+", " ")

  private def mentionLabel(a: Annotated, m: Mentioned): String = m match
    case Mentioned.Node(id) => a.byId.get(id).fold(s"- $id")(nodeLine)
    case Mentioned.Rejected(id, statement, reason) => s"- rejected $id: $statement — rejected because: $reason"
    case Mentioned.Gone(id) => s"- gone $id"
    case Mentioned.NotModelled(l) => s"- not modelled: ${flat(l)}"
    case Mentioned.Idea(l) => s"- idea: ${flat(l).take(160)}"
    case Mentioned.Term(at, v) => s"- term (at $at): $v"

  /** What the agent starts from, as text (see `Inbox`): the requests, warnings, what is the agent's to
    * do, what waits for the developer, and the tree.
    */
  def inbox(annotated: Option[Annotated], requests: List[Request]): String =
    val i = Inbox.of(annotated, requests)
    val reqs =
      if i.requests.isEmpty then List("No open requests.")
      else "Open requests from the developer:" :: i.requests.map(r =>
        s"- [${r.id}] on ${r.node.map(_.value).filter(_.nonEmpty).getOrElse("(the idea)")}: ${r.text}")
    def section(title: String, lines: List[String]) = if lines.isEmpty then Nil else "" :: title :: lines.map("- " + _)
    val rest = annotated.fold(List("", "No snapshot yet; render first.")) { _ =>
      section("Warnings (status fails on each; fix those in the code):", i.warnings) ++
        section("For you:", i.waiting.agent.map(forAgent)) ++
        section("Waiting for the developer's decision:", i.waiting.developer.map(forDeveloper))
    }
    (reqs ++ rest).mkString("\n") + annotated.fold("")(a => "\n\nThe tree:\n" + tree(a))

  private def forDeveloper(w: ForDeveloper): String = w match
    case ForDeveloper.Decide(id, cs, mechanical) =>
      s"$id: ${if cs.isEmpty then "proposed" else s"review (${cs.mkString(", ")})"}${if mechanical then ", mechanical" else ""}"
    case ForDeveloper.Gone(id) => s"$id: gone from the model; accept that it is gone"

  private def forAgent(w: ForAgent): String = w match
    // The developer's reason may ask for something in its place: the agent reads it before removing the node.
    case ForAgent.Replace(id, by, reason) =>
      s"$id: rejected by $by: ${reason.trim.stripSuffix(".")}; propose what the reason asks for in its place, or remove it from the Scala model"
    case ForAgent.Revisit(id, why) =>
      s"$id: the developer asked to revisit it ($why): propose a change, or answer on the node (answer with node) why it still holds"
    case ForAgent.Move(id, ps) => s"$id: rests on rejected ${ps.mkString(", ")}; move it under the node chosen instead"

  /** What waits for the developers, as a line of `status` (see `Load`); "" when nothing does. */
  def load(a: Annotated): String =
    val l = Load.of(a)
    if l.total == 0 then ""
    else s"Decisions waiting: ${l.total} (${l.mechanical} mechanical, decided in one batch; ${l.fresh} new and ${l.changed} changed to judge" +
      (if l.gone == 0 then ")" else s"; ${l.gone} gone from the model)") + ".\n"
