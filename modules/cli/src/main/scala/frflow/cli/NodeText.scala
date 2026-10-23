package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** How much of a node a view prints: `Brief` before a review prompt (what changed, what deciding it acts on,
  * its parts), `Normal` for `show` (about a screen: long sections cut short, lines cut to the width), `Full`
  * for `context` (everything, with what an agent reads first, nothing cut).
  */
enum Depth:
  case Brief, Normal, Full

/** A node as `show`, `context` and the review print it: what it says and why, what changed, what deciding
  * it acts on, where it sits, what it says formally, how it is proven, its examples, its code, its
  * decisions and the requests on it; at `Full` depth also the idea, what it rests on with the reasons, its
  * co-parts, the functions it calls and the obligations in Lean.
  */
object NodeText:
  private val Few = 4

  def lines(d: NodeDetails, style: Style, depth: Depth = Depth.Normal): List[String] =
    val full = depth == Depth.Full
    val st = if full then style.copy(width = None) else style
    val r = d.node
    val n = r.node
    def sec(title: String, body: List[String]) = Lines.section(title, body, st)
    val changed = if r.state == ReviewState.Review && !d.diff.isEmpty then "" :: DiffText.lines(d.diff.copy(code = d.diff.code.filterNot(_.inFull)), st) else Nil
    val partsSection = sec(n.split.fold("Parts")(sp => s"Parts: together they make it (${outcome(sp.complete, st)})"), parts(d, st))
    val out = depth match
      case Depth.Brief => header(d, st) ++ changed ++ decision(d, st, full) ++ partsSection ++
          sec("Code", governs(d, st).filter(_ => d.diff.code.exists(_.inFull)))
      case _ =>
        header(d, st) ++ changed ++ decision(d, st, full) ++
          sec("Idea (what it is decided against)", if full || r.state == ReviewState.Proposed then idea(d, st, full) else Nil) ++
          sec("Formally (as written in Scala)", formal(n)) ++
          sec("Where it sits", place(d, st, full)) ++
          (if full then d.beside.flatMap((p, co) => sec(s"Beside it under $p: together they make $p", co.map(Lines.node(_, st)))) ++
            sec("Rejected beside it", r.review.rejectedBeside.filter(_ => r.state != ReviewState.Proposed).map(x => s"${x.id}: ${x.statement} — because ${x.reason}"))
          else Nil) ++
          partsSection ++
          sec("Kept by", d.keptBy.flatMap(k => k.node.invariants.find(_.id == r.id).map(i =>
            if i.status == ObligationStatus.Exempt then s"${k.id} is exempt: ${i.detail}" else s"${k.id} (${i.status}), showing: ${i.view}"))) ++
          (if full then sec("What it rests on, nearest first, with the reasons", d.above.flatMap(above(_, st))) else Nil) ++
          sec("Vocabulary", d.terms.flatMap(t => Lines.para(s"${t.name}${if t.operation then " (operation)" else ""}: ${t.means} " +
            t.definedBy.fold("(open)")(x => s"(defined by $x)"), st))) ++
          (if full then sec("The functions it names", d.defs.flatMap(f => s"${f.name} =" :: f.source.linesIterator.map("  " + _).toList)) else Nil) ++
          sec("Proofs", proofs(n, st, full)) ++
          (if full then sec("Obligations in Lean", n.obligations.flatMap(o => s"${o.name}: ${o.description}" :: o.statement.linesIterator.map("  " + _).toList)) else Nil) ++
          sec(examplesTitle(n), examples(n, st, full)) ++
          sec("Code", code(d, st, full)) ++
          sec("Messages from the last check", n.messages.flatMap(m => if full then m.linesIterator.toList else m.linesIterator.nextOption().toList)) ++
          sec("Decisions", r.review.history.flatMap(h => line(s"${Words.date(h.at)}  ${Words.verb(h.action)} by ${h.by}: ${h.reason}", st, full))) ++
          sec("Alternatives rejected for it", r.review.alternatives.map(a => s"${a.id}: ${a.content.statement}")) ++
          sec("Requests", d.requests.flatMap(q => s"[${q.id}] ${q.status} ${st.dot} ${q.by}: ${q.text}" ::
            q.answer.filter(_.nonEmpty).map(a => s"  agent: $a").toList)) ++
          (if full then "" :: Footer else Nil)
    out.map(st.fit(_))

  val Footer: List[String] = List("A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.",
    "The developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).")

  /** Prose: wrapped in full, or one line cut to the width. */
  private def line(text: String, st: Style, full: Boolean): List[String] = if full then Lines.para(text, st) else List(text)

  private def header(d: NodeDetails, st: Style): List[String] =
    val r = d.node
    val n = r.node
    val kind = n.shownKind + n.op.fold("")(o => s" on $o") + (if d.isRoot then " (the root)" else "")
    val marks = List(Option.when(d.trusted)(st.yellow("trusted")), Option.when(d.withAgent)(st.magenta("asked of the agent")),
      n.replaces.map(x => st.dim(s"replaces $x"))).flatten
    val room = st.width.fold(Int.MaxValue)(_ - 2)
    s"${st.glyph(r)} ${st.bold(r.id.value)}  ${st.dim(kind)}  ${st.state(r.state, Lines.state(r))}${marks.map("  " + _).mkString}" ::
      st.wrap(n.content.statement, room).map("  " + _) ++
      st.wrap(s"why: ${n.content.why}", room).map(l => "  " + st.dim(l))

  /** What deciding it acts on: what it waits for, whether it is mechanical, what is not proven, the rivals it
    * rejects, the options rejected before, the decisions below; or why it was rejected.
    */
  private def decision(d: NodeDetails, st: Style, full: Boolean): List[String] =
    val r = d.node
    val v = r.review
    val open = r.state == ReviewState.Proposed || r.state == ReviewState.Review
    val rivals = d.rivals.filter(_.state != ReviewState.Rejected).map(_.id)
    val lines = if !open then Nil else
      Option.when(r.state == ReviewState.Review)(st.yellow(s"to review: ${v.causes.flatMap(Words.causes.get).mkString("; ")}")).toList ++
        v.waitsFor.map(w => st.yellow(s"decide $w first: what rests on it is decided after it")).toList ++
        (if v.mechanical then List(st.green("mechanical: Lean proves it again and nothing in it is a choice (confirm decides the batch)"))
         else v.notMechanical.filter(_ => r.state == ReviewState.Review).map(st.dim).toList) ++
        v.unproven.map(u => st.red(s"note: $u")) ++
        Option.when(rivals.nonEmpty)(s"accepting it rejects ${rivals.mkString(", ")} (its alternatives), with your reason").toList ++
        v.rejectedBeside.filter(_ => r.state == ReviewState.Proposed).map(x => st.dim(s"rejected here before: ${x.id}: ${x.statement} — because ${x.reason}")) ++
        (if v.below.isEmpty then Nil else
          "decisions below it (accept --revisit NODE reviews one again; one that moved only with it is confirmed):" ::
            v.below.flatMap(b => line(s"${b.id}${if b.kind == BelowKind.Moved then " (moved with it)" else ""}: ${b.statement} " +
              s"— holds because: ${b.reason}", st, full).map("  " + _)))
    val rejected = Option.when(r.state == ReviewState.Rejected)(v.history.reverse.find(_.action == Action.Reject)).flatten
      .map(h => st.red(s"rejected by ${h.by}: ${h.reason} (the agent removes it, or proposes what the reason asks for)")).toList
    Lines.section("Decision", lines ++ rejected, st)

  private def idea(d: NodeDetails, st: Style, full: Boolean): List[String] =
    val ls = d.idea.linesIterator.toList.flatMap(l => if l.isEmpty then List("") else Lines.para(l, st, hang = 0))
    if full || ls.size <= Few * 2 then ls else ls.take(Few * 2) :+ st.dim(s"${st.ellipsis} ${ls.size - Few * 2} more line(s): context ${d.node.id}")

  private def source(n: SnapNode, key: String): List[String] =
    n.content("sources").flatMap(_.asObject).flatMap(_(key)).flatMap(_.asString).toList.flatMap(_.linesIterator.map("  " + _))

  private def formal(n: SnapNode): List[String] =
    val sources = n.content("sources").flatMap(_.asObject).fold(Nil)(_.toList.flatMap((k, v) => v.asString.map(k -> _)))
    sources.flatMap((k, src) => s"$k${if k == "post" then n.op.fold("")(o => s" (every call of $o)") else ""}:" :: src.linesIterator.map("  " + _).toList) ++
      n.content.strs("substitutions").map("  " + _) ++
      n.invariants.flatMap(i => if i.status == ObligationStatus.Exempt then List(s"exempt from ${i.id}: ${i.detail}")
        else s"keeps ${i.id} (${i.status}), showing the rule:" :: i.view.linesIterator.map("  " + _).toList) ++
      Option.when(n.covers.nonEmpty)(s"kept by ${n.covers.mkString(", ")}").toList ++
      Option.when(n.exempts.nonEmpty)(s"exempt: ${n.exempts.mkString(", ")}").toList ++
      n.expectations.flatMap(e => s"expects (${e.status}): ${e.statement}" :: e.source.linesIterator.map("  " + _).toList)

  /** A node it rests on: its statement, the reason it holds, what it says formally. */
  private def above(a: Reviewed, st: Style): List[String] =
    Lines.node(a, st) :: (a.review.reasonNow.toList.flatMap(x => Lines.para(s"holds because: $x", st)) ++
      a.node.content("sources").flatMap(_.asObject).fold(Nil)(_.keys.toList.flatMap(source(a.node, _)))).map("  " + _)

  /** Its parents, design decisions, the definitions it uses (and what uses it), the contracts its code calls
    * (proven from their promises alone: in full, with each promise) and the code calling it; one line each.
    */
  private def place(d: NodeDetails, st: Style, full: Boolean): List[String] =
    def rows(label: String, rs: List[Reviewed], extra: Reviewed => String = _ => "") =
      rs.map(x => label.padTo(11, ' ') + Lines.node(x, st, 13, extra(x)))
    rows("part of", d.parents, partOf(_, d.node, st)) ++ rows("design", d.designs) ++ rows("uses", d.definitions) ++
      rows("used by", d.usedBy) ++
      d.calls.flatMap(c => rows("calls", List(c)) ++ (if full then source(c.node, "post").map(" " * 11 + _) else Nil)) ++
      rows("called by", d.calledBy)

  /** How it serves a parent: needed there or not, and with which co-parts. */
  private def partOf(p: Reviewed, r: Reviewed, st: Style): String =
    val need = p.node.split.flatMap(_.needed.find(_.id == r.id))
    val co = p.node.parts.filter(_ != r.id)
    st.dim(s"  ${if co.isEmpty then "its only part" else s"with ${co.mkString(", ")}"}") +
      need.filter(_.status == ObligationStatus.Shown).fold("")(x => st.red(s"; not needed: ${x.detail}"))

  /** Its parts, each with whether Lean shows it needed; whether they clash. */
  private def parts(d: NodeDetails, st: Style): List[String] =
    val sp = d.node.node.split
    d.parts.map { p =>
      val need = sp.flatMap(_.needed.find(_.id == p.id))
      Lines.node(p, st, extra = need.fold("")(x => "  " + (if x.status == ObligationStatus.Shown then st.red(s"not needed: ${x.detail}") else st.dim("needed"))))
    } ++ sp.map(s => s"clash: ${outcome(s.clash, st)}").toList

  /** An outcome in words: a try Lean found no proof of says so; otherwise its status, and the first line of
    * what Lean said (all of it, `full`).
    */
  def outcome(o: Outcome, st: Style, full: Boolean = false): String =
    val detail = if full then o.detail.linesIterator.mkString("\n    ") else o.detail.linesIterator.nextOption().getOrElse("")
    val text = if o.status == ObligationStatus.NotShown && detail.nonEmpty then detail
      else s"${o.status}${if detail.isEmpty then "" else s": $detail"}"
    if o.status.fine then st.green(text) else if o.status == ObligationStatus.Unchecked then st.dim(text) else st.red(text)

  /** Every obligation with its status, in honest words (the parts' neededness is in the parts' list). */
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

  /** The examples under the values they are given, each group once; each with its note first. Short of
    * `full`, the failing ones and the first few that pass.
    */
  private def examples(n: SnapNode, st: Style, full: Boolean): List[String] =
    val allAgree = n.examples.forall(_.lean.forall(_.status == ObligationStatus.Proven))
    val (failing, passing) = n.examples.partition(e => !e.passes || !e.lean.forall(_.status == ObligationStatus.Proven))
    val shown = if full then n.examples else n.examples.filter(e => failing.contains(e) || passing.take(Few).contains(e))
    val listed = shown.foldLeft((List.empty[String], Option.empty[List[String]])) { case ((done, last), e) =>
      val head = Option.when(!last.contains(e.`given`))(st.dim(s"given ${if e.`given`.isEmpty then "nothing" else e.`given`.mkString(", ")}")).toList
      (done ++ head :+ ("  " + example(e, st, allAgree)), Some(e.`given`))
    }._1
    listed ++ Option.when(shown.size < n.examples.size)(st.dim(s"${st.ellipsis} ${n.examples.size - shown.size} more: context ${n.id}")).toList

  private def example(e: ExampleView, st: Style, allAgree: Boolean): String =
    val mark = if e.passes then st.proven else st.failed
    val verdict = if e.passes then "" else st.red(s"  contract: ${e.fails.getOrElse("holds")}${e.codeFails.fold("")(i => s", implementation: $i")}")
    val lean = e.lean.filter(_ => !allAgree).fold("")(o => if o.status == ObligationStatus.Proven then st.dim("  Lean agrees")
      else if o.status == ObligationStatus.Failed then st.red(s"  Lean disagrees: ${o.detail}") else st.dim(s"  ${o.status} in Lean"))
    s"$mark ${e.note}$verdict$lean  ${st.dim(s"${if e.expected then "expect" else "reject"} ${e.call}")}"

  private def code(d: NodeDetails, st: Style, full: Boolean): List[String] =
    val n = d.node.node
    def runs(r: Option[String]) = r.fold("")(c => s"; running code $c checked against it")
    val how = d.codeProof.map {
      case CodeProof.ProvenDown(define, running) => s"proven define $define${runs(running)}"
      case CodeProof.Define(define, status, running) => s"define $define, $status${runs(running)}"
      case CodeProof.ByRunning => "checked by running: a plain implementation, not proven"
    }
    // The define and the running code are named above.
    val impl = n.content.text("implementation").linesIterator.filterNot(l => l.startsWith("proven: ") || l.startsWith("runs: ")).toList
    val shown = if full || impl.size <= Few + 2 then impl else impl.take(Few) :+ s"${st.ellipsis} ${impl.size - Few} more line(s): context ${n.id}"
    how.toList ++ shown.map(l => st.dim("  " + l)) ++ governs(d, st)

  private def governs(d: NodeDetails, st: Style): List[String] =
    d.node.node.code.toList.map(c => s"governs: ${c.files.mkString(", ")}" +
      (if d.diff.code.exists(_.inFull) then st.yellow(s"  (diff ${d.node.id} shows them in full: read them before accepting)") else ""))
