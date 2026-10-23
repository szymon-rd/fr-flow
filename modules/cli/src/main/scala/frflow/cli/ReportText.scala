package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** The agent-facing reports as lines: status, check, ci, find, history, and what a decision recorded. */
object ReportText:
  def status(s: StatusReport, tree: Tree, st: Style): List[String] =
    val c = s.coverage
    def ids(xs: List[NodeId]) = xs.mkString(", ")
    val splits = s"${c.splitsProven} of ${c.splits} splits proven in Lean" +
      (if c.notProvenYet.nonEmpty then s" (${ids(c.notProvenYet)} not proven yet)" else "") +
      (if c.outOfLean.nonEmpty then s" (${ids(c.outOfLean)} out of Lean)" else "")
    val contracts = s"${c.provenDown.size} of ${c.contracts} contracts proven down to their code" +
      (if c.runningBeside.nonEmpty then c.runningBeside.map(r => s"${r.node}: proven define ${r.define}; running code ${r.running} checked against it").mkString(" (", "; ", ")") else "") +
      (if c.checkedByRunning.nonEmpty then s", checked by running for ${ids(c.checkedByRunning)}" else "")
    val designs = Option.when(c.designs.nonEmpty)(s"${c.designs.size} design decision(s) govern code reviewed only (${ids(c.designs)})")
    val examples = Option.when(c.examplesInLean > 0)(s"examples evaluated in Lean as in Scala: ${c.examplesEvaluated} of ${c.examplesInLean}, and ${c.probes} probe(s) near them" +
      (if c.noneEvaluated.nonEmpty then s" (none for ${ids(c.noneEvaluated)}: unchecked, or its parameters are functions)" else ""))
    val sm = tree.summary
    val trusted = sm.rootImpl.map(r => s"Trusted (the hypotheses of root_impl, $r): ${if sm.trusted.isEmpty then "nothing" else ids(sm.trusted)}.")
    val verdict =
      if s.ok then st.green(s"${st.glyph(Glyph.Proven)} Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass.")
      else st.red(s"${st.glyph(Glyph.Failed)} Not every node is accepted, proven, and passing its examples, or there are warnings.")
    TreeText.lines(tree, st) ++ ("" :: trusted.toList) ++
      List(s"Proofs: ${(List(splits, contracts) ++ designs ++ examples).mkString("; ")}.") ++
      s.notes.map(n => st.dim(s"note: $n")) ++ s.view.warnings.map(w => st.red(s"warning: $w")) ++ List(verdict)

  def checked(c: CheckedNode, st: Style): List[String] =
    val notProven = if c.status == CheckStatus.Proven && c.notProven.nonEmpty then s" (not proven: ${c.notProven.mkString(", ")})" else ""
    val glyph = if c.ok && c.notProven.isEmpty then Glyph.Proven else if c.status == CheckStatus.Failed || c.failing.nonEmpty then Glyph.Failed else Glyph.Open
    s"${st.glyph(glyph)} ${st.bold(c.id.value)}: ${c.status}$notProven" ::
      (Option.when(c.failing.nonEmpty)(st.red(s"${c.failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof")).toList ++
        c.failing.take(5).map(f => s"  ${f.example}: ${f.verdict}") ++
        c.problems.map(r => s"${r.status} ${r.name}: ${r.detail.linesIterator.mkString("\n    ")}") ++
        c.idle.map(i => st.red(s"! doing nothing meets it ($i): state what users can do, so it says exactly what the system does (status fails until then)")) ++
        c.messages.map(m => s"! ${m.linesIterator.mkString("\n    ")}")).map("  " + _)

  def check(r: CheckReport, tree: Tree, st: Style): List[String] = r.nodes.flatMap(checked(_, st)) ++ ("" :: status(r.status, tree, st))

  def ci(r: CiReport, tree: Tree, st: Style): List[String] =
    r.notProven.flatMap(checked(_, st)) ++ (if r.notProven.isEmpty then Nil else List("")) ++ status(r.status, tree, st)

  def found(f: Found, st: Style): List[String] = f match
    case Found.Governed(_, ns) => "Governed by:" :: ns.map(Lines.node(_, st))
    case Found.Ungoverned(path) =>
      List(s"No node governs $path: code there changes unnoticed (status fails on it). Give it a home: the contract whose implementation it is, or a design node.")
    case Found.Mentions(q, Nil) =>
      List(s"No node, rejected option or not-modelled line mentions \"$q\": a new concern may need a new node (and a governed home for its code).")
    case Found.Mentions(_, hits) => "What mentions it:" :: hits.flatMap { h =>
      val what = h.kind match
        case HitKind.Node => h.id.fold("")(i => s"${st.bold(i.value)}: ")
        case HitKind.Rejected => s"rejected ${h.id.fold("")(_.value)}: "
        case HitKind.Gone => s"gone ${h.id.fold("")(_.value)}: "
        case HitKind.NotModelled => "not modelled: "
        case HitKind.Idea => "idea: "
        case HitKind.Term => s"term (at ${h.id.fold("")(_.value)}): "
      s"${st.bullet} $what${h.label}" :: h.excerpt.map(x => st.dim(s"    \"$x\"")).toList
    }

  def history(ls: List[Logged], st: Style): List[String] =
    if ls.isEmpty then List("No decisions yet.")
    else ls.flatMap(l => Lines.para(s"${Words.date(l.decision.at)}  ${st.bold(l.node.value)} ${Words.verb(l.decision.action)} by ${l.decision.by}" +
      (if l.decision.rejected.isEmpty then "" else s", rejecting ${l.decision.rejected.mkString(", ")}") + s": ${l.decision.reason}", st, indent = 0, hang = 4))

  def decided(d: Decided, st: Style): List[String] = d.decisions.map(l => s"  ${st.bullet} ${Words.decided(l)}")
