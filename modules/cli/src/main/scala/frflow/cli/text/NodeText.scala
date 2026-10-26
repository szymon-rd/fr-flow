package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** A node as `show` and the review print it; `c`, what layers on top add (a mark beside it, lines after it). */
object NodeText:
  private val Few = 4

  /** Source, diffs and decisions are wrapped to the width; prose that `show --full` shows whole is cut to it. */
  def lines(d: NodeDetails, style: Style, depth: Depth = Depth.Normal, c: Contribution = Contribution.empty): List[String] =
    val full = depth == Depth.Full
    val normal = depth != Depth.Brief
    val st = if full then style.copy(width = None) else style
    val r = d.node
    val n = r.node
    val proposal = r.state == ReviewState.Proposed
    def cut(ls: List[String]) = ls.map(st.fit(_, 2))
    val changed = if r.state != ReviewState.Review || d.diff.isEmpty then Nil
      else "" :: DiffText.lines(d.diff.copy(code = d.diff.code.filterNot(_.inFull)), st)
    // Each section: whether it shows at this depth, its title, its lines (none: no section).
    val sections: List[(Boolean, String, List[String])] = List(
      (normal, "Idea (what it is decided against)", if full || proposal then idea(d, st, full) else Nil),
      (normal || proposal, "Formally (as written in Scala)", formal(n)),
      (normal, "Where it sits", place(d, st, full))
    ) ++ d.beside.map((p, co) => (full, s"Beside it under $p: together they make $p", co.map(Lines.node(_, st)))) ++ List(
      (full && !proposal, "Rejected beside it", r.review.rejectedBeside.map(x => s"${x.id}: ${x.statement} — because ${x.reason}")),
      (true, n.split.fold("Parts")(sp => s"Parts: together they make it (${outcome(sp.complete, st)})"), parts(d, st)),
      (normal, "Kept by", d.keptBy.flatMap(k => k.node.invariants.find(_.id == r.id).map(i =>
        if i.status == ObligationStatus.Exempt then s"${k.id} is exempt: ${i.detail}" else s"${k.id} (${i.status}), showing: ${i.view}"))),
      (full, "What it rests on, nearest first, with the reasons", d.above.flatMap(above(_, st))),
      (normal, "Vocabulary", d.terms.flatMap(t => Lines.para(s"${t.name}${if t.operation then " (operation)" else ""}: ${t.means} " +
        t.definedBy.fold("(open)")(x => s"(defined by $x)"), st))),
      (full, "The functions it names", d.defs.flatMap(f => s"${f.name} =" :: indent(f.source))),
      (normal, "Proofs", cut(proofs(n, st, full))),
      (full, "Obligations in Lean", n.obligations.flatMap(o => s"${o.name}: ${o.description}" :: indent(o.statement))),
      (normal, examplesTitle(n), cut(examples(n, st, full))),
      (normal, "Code", code(d, st, full)),
      (!normal, "Code", governs(d, st).filter(_ => d.diff.code.exists(_.inFull))),
      (normal, "Messages from the last check", cut(n.messages.flatMap(m => if full then m.linesIterator.toList else m.linesIterator.nextOption().toList))),
      (normal, "Decisions", r.review.history.flatMap(h => st.fold(s"${Words.date(h.at)}  ${Words.verb(h.action)} by ${h.by}: ${h.reason}", 2))),
      (normal, "Alternatives rejected for it", cut(r.review.alternatives.map(a => s"${a.id}: ${a.content.statement}"))))
    val body = sections.flatMap((shown, title, ls) => if shown then Lines.section(title, ls, st) else Nil)
    (header(d, st, c.marks.get(r.id)) ++ changed ++ decision(d, st) ++ body ++ (if normal then c.node(r.id, st) else Nil)).flatMap(st.fold(_))

  private def indent(s: String): List[String] = s.linesIterator.map("  " + _).toList

  private def header(d: NodeDetails, st: Style, mark: Option[String]): List[String] =
    val r = d.node
    val n = r.node
    val kind = n.shownKind + n.op.fold("")(o => s" on $o") + (if d.isRoot then " (the root)" else "")
    val marks = List(Option.when(d.trusted)(st.yellow("trusted")), mark.map(st.magenta),
      n.replaces.map(x => st.dim(s"replaces $x"))).flatten
    val room = st.width.fold(Int.MaxValue)(_ - 2)
    s"${st.glyph(r)} ${st.bold(r.id.value)}  ${st.dim(kind)}  ${st.state(r.state, Lines.state(r))}${marks.map("  " + _).mkString}" ::
      st.wrap(n.content.statement, room).map("  " + _) ++ st.wrap(s"why: ${n.content.why}", room).map(l => "  " + st.dim(l))

  /** What deciding it acts on; or why it was rejected. */
  private def decision(d: NodeDetails, st: Style): List[String] =
    val r = d.node
    val v = r.review
    val open = r.state == ReviewState.Proposed || r.state == ReviewState.Review
    val rivals = d.rivals.filter(_.state != ReviewState.Rejected).map(_.id)
    val lines = if !open then Nil else
      Option.when(r.state == ReviewState.Review)(st.yellow(s"to review: ${v.causes.flatMap(Words.causes.get).mkString("; ")}")).toList ++
        v.waitsFor.map(w => st.yellow(s"decide $w first: what rests on it is decided after it")).toList ++
        (if v.mechanical then List(st.green("mechanical: Lean proves it again and nothing in it is a choice (confirm decides the batch)"))
         else v.notMechanical.filter(_ => r.state == ReviewState.Review && v.waitsFor.isEmpty).map(st.dim).toList) ++
        v.unproven.map(u => st.red(s"note: $u")) ++
        Option.when(rivals.nonEmpty)(s"accepting it rejects ${rivals.mkString(", ")} (its alternatives), with your reason").toList ++
        v.rejectedBeside.filter(_ => r.state == ReviewState.Proposed).map(x => st.dim(s"rejected here before: ${x.id}: ${x.statement} — because ${x.reason}")) ++
        (if v.below.isEmpty then Nil else
          "decisions below it (accept --revisit NODE reviews one again; one that moved only with it is confirmed):" ::
            v.below.flatMap(b => st.fold(s"  ${b.id}${if b.kind == BelowKind.Moved then " (moved with it)" else ""}: ${b.statement} " +
              s"— holds because: ${b.reason}", 2)))
    val rejected = Option.when(r.state == ReviewState.Rejected)(v.history.reverse.find(_.action == Action.Reject)).flatten
      .map(h => st.red(s"rejected by ${h.by}: ${h.reason} (remove it from the model, or propose what the reason asks for instead)")).toList
    Lines.section("Decision", lines ++ rejected, st)

  private def idea(d: NodeDetails, st: Style, full: Boolean): List[String] =
    val ls = d.idea.linesIterator.toList.flatMap(l => if l.isEmpty then List("") else Lines.para(l, st, hang = 0))
    if full || ls.size <= Few * 2 then ls else ls.take(Few * 2) :+ st.dim(s"${st.ellipsis} ${ls.size - Few * 2} more line(s): context ${d.node.id}")

  private def sources(n: SnapNode): List[(String, String)] =
    n.content("sources").flatMap(_.asObject).fold(Nil)(_.toList.flatMap((k, v) => v.asString.map(k -> _)))

  private def formal(n: SnapNode): List[String] =
    sources(n).flatMap((k, src) => s"$k${if k == "post" then n.op.fold("")(o => s" (every call of $o)") else ""}:" :: indent(src)) ++
      n.content.strs("substitutions").map("  " + _) ++
      // A boundary's model, as Lean has it: what the developer decides the outside does.
      Option.when(n.content.strs("model").nonEmpty)("model:").toList ++ n.content.strs("model").flatMap(indent) ++
      n.invariants.flatMap(i => if i.status == ObligationStatus.Exempt then List(s"exempt from ${i.id}: ${i.detail}")
        else s"keeps ${i.id} (${i.status}), showing the rule:" :: indent(i.view)) ++
      Option.when(n.covers.nonEmpty)(s"kept by ${n.covers.mkString(", ")}").toList ++
      Option.when(n.exempts.nonEmpty)(s"exempt: ${n.exempts.mkString(", ")}").toList ++
      n.expectations.flatMap(e => s"expects (${e.status}): ${e.statement}" :: indent(e.source))

  private def above(a: Reviewed, st: Style): List[String] =
    Lines.node(a, st) :: (a.review.reasonNow.toList.flatMap(x => Lines.para(s"holds because: $x", st)) ++
      sources(a.node).flatMap((_, src) => indent(src))).map("  " + _)

  /** One line each; a contract its code calls is proven from its promise alone, so `full` shows the promise. */
  private def place(d: NodeDetails, st: Style, full: Boolean): List[String] =
    def rows(label: String, rs: List[Reviewed], extra: Reviewed => String = _ => "") =
      rs.map(x => label.padTo(11, ' ') + Lines.node(x, st, 13, extra(x)))
    rows("part of", d.parents, partOf(_, d.node, st)) ++ rows("design", d.designs) ++ rows("uses", d.definitions) ++ rows("used by", d.usedBy) ++
      d.calls.flatMap(c => rows("calls", List(c)) ++ (if full then sources(c.node).filter(_._1 == "post").flatMap((_, src) => indent(src)).map(" " * 11 + _) else Nil)) ++
      rows("called by", d.calledBy)

  private def partOf(p: Reviewed, r: Reviewed, st: Style): String =
    val need = p.node.split.flatMap(_.needed.find(_.id == r.id))
    val co = p.node.parts.filter(_ != r.id)
    st.dim(s"  ${if co.isEmpty then "its only part" else s"with ${co.mkString(", ")}"}") +
      need.filter(_.status == ObligationStatus.Shown).fold("")(x => st.red(s"; not needed: ${x.detail}"))

  private def parts(d: NodeDetails, st: Style): List[String] =
    val sp = d.node.node.split
    d.parts.map { p =>
      val need = sp.flatMap(_.needed.find(_.id == p.id))
      Lines.node(p, st, extra = need.fold("")(x => "  " + (if x.status == ObligationStatus.Shown then st.red(s"not needed: ${x.detail}") else st.dim("needed"))))
    } ++ sp.map(s => s"clash: ${outcome(s.clash, st)}").toList

  /** A try Lean found no proof of says what it tried; otherwise the status, and the first line of what Lean said. */
  private def outcome(o: Outcome, st: Style, full: Boolean = false): String =
    val detail = if full then o.detail.linesIterator.mkString("\n    ") else o.detail.linesIterator.nextOption().getOrElse("")
    val text = if o.status == ObligationStatus.NotShown && detail.nonEmpty then detail
      else s"${o.status}${if detail.isEmpty then "" else s": $detail"}"
    if o.status.fine then st.green(text) else if o.status == ObligationStatus.Unchecked then st.dim(text) else st.red(text)

  private def proofs(n: SnapNode, st: Style, full: Boolean): List[String] =
    n.split.map(sp => s"complete: ${outcome(sp.complete, st, full)}").toList ++
      n.implementationProof.map(p => s"impl (${p.name}): ${outcome(Outcome(p.status, p.detail), st, full)}") ++
      n.rootImpl.map(o => s"root_impl: ${outcome(o, st, full)}") ++
      n.idle.map(i => st.red(s"idle: Lean shows doing nothing meets it ($i): say what users can do")) ++
      n.status.filter(_ != CheckStatus.Proven).map(s => st.yellow(s"check: $s"))

  private def examplesTitle(n: SnapNode): String =
    val (ok, total) = n.examplesPassing
    val lean = n.examples.flatMap(_.lean)
    s"Examples: $ok of $total pass" + (if lean.isEmpty then "" else s"; Lean agrees on ${lean.count(_.status == ObligationStatus.Proven)} of ${lean.size}")

  /** Grouped under the values they are given; short of `full`, the failing ones and the first few that pass. */
  private def examples(n: SnapNode, st: Style, full: Boolean): List[String] =
    val allAgree = n.examples.forall(_.lean.forall(_.status == ObligationStatus.Proven))
    val (failing, passing) = n.examples.partition(e => !e.passes || !e.lean.forall(_.status == ObligationStatus.Proven))
    val shown = if full then n.examples else n.examples.filter(e => failing.contains(e) || passing.take(Few).contains(e))
    shown.zip(None :: shown.map(e => Some(e.`given`))).flatMap((e, before) =>
      Option.when(!before.contains(e.`given`))(st.dim(s"given ${if e.`given`.isEmpty then "nothing" else e.`given`.mkString(", ")}")).toList :+
        ("  " + example(e, st, allAgree))) ++
      Option.when(shown.size < n.examples.size)(st.dim(s"${st.ellipsis} ${n.examples.size - shown.size} more: context ${n.id}")).toList

  private def example(e: ExampleView, st: Style, allAgree: Boolean): String =
    val mark = if e.passes then st.proven else st.failed
    val verdict = if e.passes then "" else st.red(s"  contract: ${e.fails.getOrElse("holds")}${e.codeFails.fold("")(i => s", implementation: $i")}")
    val lean = e.lean.filter(_ => !allAgree).fold("")(o => if o.status == ObligationStatus.Proven then st.dim("  Lean agrees")
      else if o.status == ObligationStatus.Failed then st.red(s"  Lean disagrees: ${o.detail}") else st.dim(s"  ${o.status} in Lean"))
    s"$mark ${e.note}$verdict$lean  ${st.dim(s"${if e.expected then "expect" else "reject"} ${e.call}")}"

  private def code(d: NodeDetails, st: Style, full: Boolean): List[String] =
    val n = d.node.node
    def runs(r: Option[String]) = r.fold("")(c => s"; running code $c tested against it")
    val how = d.codeProof.map {
      case CodeProof.ProvenDown(define, running) => s"proven define $define${runs(running)}"
      case CodeProof.Define(define, status, running) => s"define $define, $status${runs(running)}"
      case CodeProof.Tested(_) => "plain code, tested against the contract, not proven"
      case CodeProof.Model(own, outside, _) =>
        "implemented by: " + (own.map(i => s"$i (the project's own code, tested against the model)") ++
          outside.map(i => s"$i (an outside system, checked against the model; the model stays assumed)")).mkString("; ")
    }
    // The define and the running code are named above.
    val impl = n.content.text("implementation").linesIterator.filterNot(l => l.startsWith("proven: ") || l.startsWith("runs: ")).toList
    val shown = if full || impl.size <= Few + 2 then impl else impl.take(Few) :+ s"${st.ellipsis} ${impl.size - Few} more line(s): context ${n.id}"
    how.toList ++ shown.map(l => st.dim("  " + l)) ++ tests(n, st, full) ++ n.runtime.map(_.describe).toList ++ governs(d, st)

  /** What the tests of the code found: cases, seed, the failing case (shrunk), how often each part of the contract (or
    * each operation and branch of the model) was reached.
    */
  private def tests(n: SnapNode, st: Style, full: Boolean): List[String] =
    val model = CodeProof.of(n).exists { case _: CodeProof.Model => true; case _ => false }
    if !CodeProof.run(n) then Nil
    else n.tested.fold(List(st.yellow("tested: not yet (run check)"))) { r =>
      val head = s"tested: ${f"${r.cases}%,d"} generated ${if model then "runs of its operations" else "cases"} (seed ${r.seed}), against ${r.against}"
      val pass = if model then "  every run gives what the model gives and leaves what it leaves, and every operation and branch of it was reached"
        else "  every case meets it, and every part of it was reached"
      val outcome = r.failure.fold(Option.when(r.unreached.isEmpty)(st.green(pass)).toList)(f =>
        List(st.red(s"  fails: ${f.line}")))
      val parts = if full || r.unreached.nonEmpty then r.coverage.map(c =>
        if c.held == 0 then st.red(s"  never reached: ${c.part}") else st.dim(s"  ${c.part}: ${c.held}×")) else Nil
      val notes = r.notes.map(x => st.dim(s"  note: $x"))
      (head :: outcome) ++ parts ++ notes
    }

  private def governs(d: NodeDetails, st: Style): List[String] =
    d.node.node.code.toList.map(c => s"governs: ${c.files.mkString(", ")}" +
      (if d.diff.code.exists(_.inFull) then st.yellow(s"  (diff ${d.node.id} shows them in full: read them before accepting)") else ""))
