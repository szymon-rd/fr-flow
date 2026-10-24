package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** The DAG from the root, each node once under its first parent and `⇢ X` under the others; `c`, what layers on top add. */
object TreeText:
  def lines(t: Tree, st: Style, c: Contribution = Contribution.empty): List[String] =
    def rows(n: TreeNode, prefix: String, cont: String): List[String] =
      val r = n.node
      val head = s"$prefix${st.glyph(r)} ${st.bold(r.id.value)}${Lines.marks(r, st, c.marks.get(r.id))}  "
      val kids = n.children.map(Left(_)) ++ n.seeAlso.map(Right(_))
      // The root is read whole: wrapped at its clauses, under its statement, not cut.
      val row =
        if r.node.parents.isEmpty && prefix.isEmpty && r.node.kind == NodeKind.Claim then
          Lines.clauses(Lines.statement(r), st, Style.visible(head), if kids.isEmpty then "" else st.bar) match
            case first :: rest => (head + first) :: rest
            case Nil           => List(head)
        else List(st.fit(head + Lines.statement(r)))
      row ++ kids.zipWithIndex.flatMap { (k, i) =>
        val end = i == kids.size - 1
        val (p, c) = (cont + (if end then st.last else st.tee), cont + (if end then "   " else st.bar))
        k.fold(rows(_, p, c), id => List(st.dim(s"$p${st.see} $id")))
      }
    def section(title: String, ns: List[TreeNode]) =
      if ns.isEmpty then Nil else (if title.isEmpty then Nil else List("", st.bold(title))) ++ ns.flatMap(rows(_, "", ""))
    val gone = if t.gone.isEmpty then Nil
      else "" :: st.bold("Gone from the model: accept that each is gone (gone NODE)") ::
        t.gone.map(g => st.fit(s"${st.red(st.dot)} ${st.bold(g.id.value)}  ${st.dim(g.decision.content.statement)}"))
    (section("", t.main) ++ section("Assumptions, under no parent: trusted (the code calls them)", t.assumptions) ++
      section("Under no parent", t.unparented) ++ section("Definitions: they fix terms of the vocabulary (decided, not proven)", t.definitions))
      .dropWhile(_.isEmpty) ++ gone ++ ("" :: SummaryText.lines(t.overview, st, c.waiting(st)))

/** The lines every view closes with: the counts, the proofs and what is trusted, what waits; `more`, what layers on top
  * add to what waits.
  */
object SummaryText:
  def lines(s: Overview, st: Style, more: List[String] = Nil): List[String] =
    def some(n: Int, what: String, tone: String => String = identity) = Option.when(n > 0)(tone(s"$n $what"))
    val counts = (Some(st.green(s"${s.accepted} accepted")) :: List(some(s.review, "to review", st.yellow),
      some(s.proposed, "proposed", st.cyan), some(s.rejected, "rejected", st.red), some(s.gone, "gone", st.red))).flatten
    def ratio(ok: Int, of: Int) = if ok == of then st.green(s"$ok/$of") else st.red(s"$ok/$of")
    val rootImpl = s.rootImpl.map {
      case ObligationStatus.Proven => st.green("proven")
      case ObligationStatus.Unchecked => st.dim("unchecked")
      case other => st.red(other.toString)
    }
    val proofs = List(Option.when(s.splits > 0)(s"splits ${ratio(s.splitsProven, s.splits)} proven"),
      Option.when(s.contracts > 0)(s"contracts ${ratio(s.contractsProvenDown, s.contracts)} proven down to their code"),
      Option.when(s.contractsTested > 0)(s"code tested against its contract ${ratio(s.testsPassing, s.contractsTested)}"),
      rootImpl.map(r => s"root_impl $r"),
      Option.when(s.examplesInLean > 0)(s"examples ${ratio(s.examplesAgreeing, s.examplesInLean)} agree in Lean"),
      Some(s"trusted: ${s.trusted.filterNot(s.tested.contains) match { case Nil => "nothing"; case ts => ts.mkString(", ") }}" +
        (if s.tested.isEmpty then "" else s"; tested, not proven: ${s.tested.mkString(", ")}")),
      some(s.unproven, "with something unproven", st.red), some(s.warnings, "warning(s)", st.red),
      some(s.unsigned, "decision(s) not signed", st.red)).flatten
    val waits = List(
      Option.when(s.forDeveloper > 0)(st.yellow(s"${s.forDeveloper} for the developer") +
        (if s.idea.exists(_ != ReviewState.Accepted) then " (IDEA.md first)" else "") +
        (if s.mechanical > 0 then s" (${s.mechanical} mechanical: confirm)" else ""))).flatten ++ more
    val sep = if st.unicode then s" ${st.dot} " else ", "
    // Before the first node, the project is IDEA.md: what comes next is said instead of the counts.
    val start = if s.nodes > 0 then Nil
      else List(s.idea match
        case None => "No IDEA.md yet: write in it what the system is for, then accept it; the root comes next."
        case Some(ReviewState.Accepted) => "IDEA.md is accepted: the root comes next."
        case Some(_) => "IDEA.md waits for you: read it, then accept IDEA.")
    val head = if s.nodes > 0 then List(s"${st.bold(s.name)}: ${s.nodes} nodes${sep}${counts.mkString(sep)}", proofs.mkString(sep))
      else List(s"${st.bold(s.name)}: no nodes yet") ++ start
    (head :+ (if waits.isEmpty then (if s.complete then st.green(s"Nothing waits: every node is accepted and proven${if s.tested.isEmpty then "" else ", or its code tested"}.") else "Nothing waits for a decision.")
      else s"Waiting: ${waits.mkString(sep)}")).flatMap(Lines.para(_, st, indent = 0))

/** What waits for the developer; then what layers on top add (`c`); the summary last. */
object InboxText:
  import Lines.section

  /** `v`: the view the inbox was read from, for a gone node renamed. */
  def lines(i: Inbox, v: View, st: Style, c: Contribution = Contribution.empty): List[String] =
    def waiting(w: Queued) =
      Lines.node(w.node, st, 4, w.waitsFor.fold("")(x => st.dim(s"  after $x"))) ::
        w.followers.map(f => st.dim("  " + Words.follower(f, w.node.id, st)))
    val idea = i.idea.toList.flatMap { r =>
      val how = if r.state == ReviewState.Review then "changed since you accepted it" else "not accepted yet"
      Lines.para(s"${st.bold("IDEA")}  ${st.yellow(s"IDEA.md, $how")}: read it, then accept IDEA (the root is decided after it)", st)
    }
    val body =
      section("IDEA.md, first", idea, st) ++
        section("Warnings: status fails on each", (i.warnings ++ c.warnings).map(w => st.red(s"${st.bullet} $w")), st) ++
        section("For the developer, in order (review, or accept / reject NODE)", i.queue.flatMap(waiting), st) ++
        section(s"Mechanical: Lean proves them again, nothing in them is a choice (confirm decides all ${i.mechanical.size})",
          i.mechanical.map(Lines.node(_, st, 4)), st) ++
        section("Gone from the model (gone NODE)", i.gone.map(Details.gone(v, _)).map(g => st.fit(s"${st.bold(g.gone.id.value)}" +
          s"${g.renamedTo.fold("")(y => st.yellow(s"  renamed to $y"))}: ${g.gone.decision.content.statement}", 2)), st) ++
        c.inbox(st)
    (body ++ ("" :: SummaryText.lines(i.overview, st, c.waiting(st)))).dropWhile(_.isEmpty)

/** The reports of status, check, ci and find; and what a decision recorded. `c`: what layers on top add. */
object ReportText:
  def status(v: View, tree: Tree, st: Style, c: Contribution = Contribution.empty): List[String] =
    TreeText.lines(tree, st, c) ++ (v.warnings ++ c.warnings).map(w => st.red(s"warning: $w"))

  private def checked(c: CheckedNode, st: Style): List[String] =
    // Its status as `check` exits on (`ok`): proven by Lean with an obligation open, or an example failing, is not proven.
    val status = if c.status != CheckStatus.Proven || c.ok then c.status else if c.notProven.isEmpty then CheckStatus.Failed else CheckStatus.Open
    val notProven = if status != c.status && c.notProven.nonEmpty then s" (${c.notProven.mkString(", ")} not proven)" else ""
    val glyph = if c.ok then st.proven else if status == CheckStatus.Failed || c.failing.nonEmpty then st.failed else st.open
    s"$glyph ${st.bold(c.id.value)}: $status$notProven" ::
      (Option.when(c.failing.nonEmpty)(st.red(s"${c.failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof")).toList ++
        c.failing.take(5).map(f => s"  ${f.example}: ${f.verdict}") ++
        c.problems.map(r => s"${r.name} ${r.status}: ${r.detail.linesIterator.mkString("\n    ")}") ++
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
