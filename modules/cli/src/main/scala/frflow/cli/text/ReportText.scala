package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** The reports of status, check, ci and find; and what a decision recorded. `c`: what layers on top add. */
object ReportText:
  def status(v: View, tree: Tree, st: Style, c: Contribution = Contribution.empty): List[String] =
    TreeText.lines(tree, st, c) ++ (v.warnings ++ c.warnings).map(w => st.red(s"warning: $w"))

  private def checked(c: CheckedNode, st: Style): List[String] =
    // Its status as `check` exits on (`ok`): proven by Lean with an obligation open, or an example failing, is not proven.
    val status = if c.status != CheckStatus.Proven || c.ok then c.status else if c.notProven.isEmpty then CheckStatus.Failed else CheckStatus.Open
    val notProven = if status != c.status && c.notProven.nonEmpty then s" (${c.notProven.mkString(", ")} not proven)" else ""
    val glyph = if c.ok then st.proven else if status == CheckStatus.Failed || c.failing.nonEmpty then st.failed else st.open
    // One obligation left: what it says is the node's line, its name left out; several are listed by name.
    val (head, problems) = c.problems match
      case List(r) =>
        val ls = r.detail.linesIterator.toList
        (ls.headOption.filter(_.trim.nonEmpty).getOrElse(s"$status$notProven"), ls.drop(1) match { case Nil => Nil; case rest => List("  " + rest.mkString("\n    ")) })
      case rs => (s"$status$notProven", rs.map(r => s"${r.name} ${r.status}: ${r.detail.linesIterator.mkString("\n    ")}"))
    s"$glyph ${st.bold(c.id.value)}: $head" ::
      (Option.when(c.failing.nonEmpty)(st.red(s"${c.failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof")).toList ++
        c.failing.take(5).map(f => s"  ${f.example}: ${f.verdict}") ++
        c.testFailure.toList.map(f => st.red(s"its code fails a generated case: ${f.line}")) ++
        problems ++
        c.idle.map(i => st.red(s"! doing nothing meets it ($i): state what users can do, so it says exactly what the system does (status fails until then)")) ++
        (c.messages ++ c.hint).map(m => s"! ${m.linesIterator.mkString("\n    ")}")).map("  " + _)

  def check(r: CheckReport, st: Style, c: Contribution = Contribution.empty): List[String] =
    r.nodes.flatMap(checked(_, st)) ++ ("" :: SummaryText.lines(r.overview, st, c.waiting(st))) ++
      (r.view.warnings ++ c.warnings).map(w => st.red(s"warning: $w"))

  def ci(r: CiReport, tree: Tree, st: Style, c: Contribution = Contribution.empty): List[String] =
    r.notProven.flatMap(checked(_, st)) ++ (if r.notProven.isEmpty then Nil else List("")) ++ status(r.view, tree, st, c)

  /** Each node in one line, each mention with its sentence. */
  def found(f: Found, v: View, st: Style): List[String] = f match
    case Found.Governed(_, ids) => "Governed by:" :: ids.flatMap(v.node).map(Lines.node(_, st))
    case Found.Missing(path) =>
      Lines.para(s"There is no file or directory $path (paths are relative to the project's directory).", st, indent = 0)
    case Found.Ungoverned(path) =>
      Lines.para(s"No node governs $path: code there changes unnoticed (status fails on a source file no node governs). Give it a home: the contract whose implementation it is, or a design node.", st, indent = 0)
    case Found.Nothing(q) =>
      Lines.para(s"No node, rejected option or not-modelled line mentions \"$q\": a new concern may need a new node (and a governed home for its code).", st, indent = 0)
    case Found.Mentions(_, ms) => "What mentions it:" :: ms.flatMap { m =>
      def flat(s: String) = s.replaceAll("\\s+", " ").trim
      val label = m.what match
        case Mentioned.Node(id) => s"${st.bold(id.value)}: ${v.node(id).fold("")(Lines.statement)}"
        case Mentioned.Rejected(id, statement, reason) => s"rejected $id: $statement — rejected because: $reason"
        case Mentioned.Gone(id) => s"gone $id: ${v.annotated.gone.find(_.id == id).fold("")(g => flat(g.decision.content.statement))}"
        case Mentioned.NotModelled(line) => s"not modelled: ${flat(line)}"
        case Mentioned.Idea(line) => s"idea: ${flat(line).take(160)}"
        case Mentioned.Term(at, meaning) => s"term (at $at): $meaning"
      Lines.para(s"${st.bullet} $label", st, indent = 0) ++
        m.sentence.filterNot(x => Style.strip(label).contains(x)).toList.flatMap(x => Lines.para(s"\"${x.take(200)}\"", st, indent = 4).map(l => st.dim("    " + l)))
    }

  /** `notes`: with what is not proven of the nodes it accepts. */
  def decided(d: Decided, st: Style, notes: Boolean = true): List[String] = d.decisions.map(l => s"  ${st.bullet} ${Words.decided(l)}") ++
    (if notes then d.unproven.map((id, u) => st.yellow(s"  note: $id: $u")) else Nil)
