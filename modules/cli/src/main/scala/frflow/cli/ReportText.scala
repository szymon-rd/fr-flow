package frflow.cli

import frflow.api.*
import frflow.ledger.{Found, Mentioned}
import frflow.protocol.*

/** The agent-facing reports as lines: status, check, ci, find, history, and what a decision recorded. */
object ReportText:
  /** Where the knowledge base stands: the tree, what the root's proof trusts, how far the proofs reach. */
  def status(v: View, tree: Tree, st: Style): List[String] =
    val c = v.status.reach
    def ids(xs: List[NodeId]) = xs.mkString(", ")
    val splits = s"${c.provenSplits} of ${c.splits} splits proven in Lean" +
      (if c.notProvenYet.nonEmpty then s" (${ids(c.notProvenYet)} not proven yet)" else "") +
      (if c.outOfLean.nonEmpty then s" (${ids(c.outOfLean)} out of Lean)" else "")
    val contracts = s"${c.provenDown.size} of ${c.contracts} contracts proven down to their code" +
      (if c.beside.nonEmpty then c.beside.map(r => s"${r.node}: proven define ${r.define}; running code ${r.running} checked against it").mkString(" (", "; ", ")") else "") +
      (if c.byRunning.nonEmpty then s", checked by running for ${ids(c.byRunning)}" else "")
    val designs = Option.when(c.designs.nonEmpty)(s"${c.designs.size} design decision(s) govern code reviewed only (${ids(c.designs)})")
    val examples = c.examples.map(e => s"examples evaluated in Lean as in Scala: ${e.evaluated} of ${e.total}, and ${e.probes} probe(s) near them" +
      (if e.none.nonEmpty then s" (none for ${ids(e.none)}: unchecked, or its parameters are functions)" else ""))
    val o = tree.overview
    val trusted = o.rootImpl.map(r => s"Trusted (the hypotheses of root_impl, $r): ${if o.decisions.trusted.isEmpty then "nothing" else ids(o.decisions.trusted)}.")
    val verdict =
      if v.status.ok then st.green(s"${st.glyph(Glyph.Proven)} Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass.")
      else st.red(s"${st.glyph(Glyph.Failed)} Not every node is accepted, proven, and passing its examples, or there are warnings.")
    TreeText.lines(tree, st) ++ ("" :: trusted.toList) ++
      List(s"Proofs: ${(List(splits, contracts) ++ designs ++ examples).mkString("; ")}.") ++
      v.status.notes.map(n => st.dim(s"note: $n")) ++ v.warnings.map(w => st.red(s"warning: $w")) ++ List(verdict)

  def checked(c: CheckedNode, st: Style): List[String] =
    val notProven = if c.status == CheckStatus.Proven && c.notProven.nonEmpty then s" (not proven: ${c.notProven.mkString(", ")})" else ""
    val glyph = if c.ok && c.notProven.isEmpty then Glyph.Proven else if c.status == CheckStatus.Failed || c.failing.nonEmpty then Glyph.Failed else Glyph.Open
    s"${st.glyph(glyph)} ${st.bold(c.id.value)}: ${c.status}$notProven" ::
      (Option.when(c.failing.nonEmpty)(st.red(s"${c.failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof")).toList ++
        c.failing.take(5).map(f => s"  ${f.example}: ${f.verdict}") ++
        c.problems.map(r => s"${r.status} ${r.name}: ${r.detail.linesIterator.mkString("\n    ")}") ++
        c.idle.map(i => st.red(s"! doing nothing meets it ($i): state what users can do, so it says exactly what the system does (status fails until then)")) ++
        c.messages.map(m => s"! ${m.linesIterator.mkString("\n    ")}")).map("  " + _)

  def check(r: CheckReport, tree: Tree, st: Style): List[String] = r.nodes.flatMap(checked(_, st)) ++ ("" :: status(r.view, tree, st))

  def ci(r: CiReport, tree: Tree, st: Style): List[String] =
    r.notProven.flatMap(checked(_, st)) ++ (if r.notProven.isEmpty then Nil else List("")) ++ status(r.view, tree, st)

  /** Where a change belongs (see the ledger's `Find`): each node in one line, each mention with its sentence. */
  def found(f: Found, v: View, st: Style): List[String] = f match
    case Found.Governed(_, ids) => "Governed by:" :: ids.flatMap(v.node).map(Lines.node(_, st))
    case Found.Ungoverned(path) =>
      List(s"No node governs $path: code there changes unnoticed (status fails on it). Give it a home: the contract whose implementation it is, or a design node.")
    case Found.Nothing(q) =>
      List(s"No node, rejected option or not-modelled line mentions \"$q\": a new concern may need a new node (and a governed home for its code).")
    case Found.Mentions(_, ms) => "What mentions it:" :: ms.flatMap { m =>
      def flat(s: String) = s.replaceAll("\\s+", " ").trim
      val label = m.what match
        case Mentioned.Node(id) => s"${st.bold(id.value)}: ${v.node(id).fold("")(r => flat(r.node.content.statement))}"
        case Mentioned.Rejected(id, statement, reason) => s"rejected $id: $statement — rejected because: $reason"
        case Mentioned.Gone(id) => s"gone $id: ${v.annotated.gone.find(_.id == id).fold("")(g => flat(g.decision.content.statement))}"
        case Mentioned.NotModelled(line) => s"not modelled: ${flat(line)}"
        case Mentioned.Idea(line) => s"idea: ${flat(line).take(160)}"
        case Mentioned.Term(at, meaning) => s"term (at $at): $meaning"
      s"${st.bullet} $label" :: m.sentence.filterNot(x => Style.strip(label).contains(x)).map(x => st.dim(s"    \"${x.take(200)}\"")).toList
    }

  def history(ls: List[Logged], st: Style): List[String] =
    if ls.isEmpty then List("No decisions yet.")
    else ls.flatMap(l => Lines.para(s"${Words.date(l.decision.at)}  ${st.bold(l.node.value)} ${Words.verb(l.decision.action)} by ${l.decision.by}" +
      (if l.decision.rejected.isEmpty then "" else s", rejecting ${l.decision.rejected.mkString(", ")}") + s": ${l.decision.reason}", st, indent = 0, hang = 4))

  def decided(d: Decided, st: Style): List[String] = d.decisions.map(l => s"  ${st.bullet} ${Words.decided(l)}")
