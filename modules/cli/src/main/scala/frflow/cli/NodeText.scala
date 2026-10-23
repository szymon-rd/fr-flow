package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** A node as `show` and the review print it: what it says and why, what changed, what deciding it acts
  * on, where it sits, what it says formally, how it is proven, its examples, its code, its decisions and
  * the requests on it. `lean` adds the generated Lean and the obligations' statements.
  */
object NodeText:
  def lines(d: NodeDetails, st: Style, lean: Boolean = false): List[String] =
    val r = d.node
    val n = r.node
    header(d, st) ++
      (if r.state == ReviewState.Review && !d.diff.isEmpty then "" :: DiffText.lines(d.diff.copy(code = d.diff.code.filterNot(_.inFull)), st) else Nil) ++
      decision(d, st) ++
      Lines.section("What it rests on, with the reasons",
        d.above.filter(_ => r.state == ReviewState.Proposed).filter(_.review.reasonNow.isDefined)
          .flatMap(a => Lines.para(s"${a.id}: ${a.review.reasonNow.getOrElse("")}", st)), st) ++
      Lines.section("Idea (what it is decided against)", (n.content.text("idea").linesIterator.toList ++
        Option.when(n.content.text("notModelled").nonEmpty)("" :: "Not modelled:" :: n.content.text("notModelled").linesIterator.toList).toList.flatten)
        .flatMap(l => if l.isEmpty then List("") else Lines.para(l, st, hang = 0)), st) ++
      Lines.section("Formally (as written in Scala)", formal(n), st) ++
      Lines.section("Parents: it is a part of each", d.parents.map(p => Lines.node(p, st, extra = partOf(p, r, st))), st) ++
      Lines.section(n.split.fold("Parts")(sp => s"Parts: together they make it (${outcome(sp.complete, st)})"), parts(d, st), st) ++
      Lines.section("Design decisions under it", d.designs.map(Lines.node(_, st)), st) ++
      Lines.section("Definitions in force it uses", d.definitions.map(Lines.node(_, st)), st) ++
      Lines.section("Used by", d.usedBy.map(Lines.node(_, st)), st) ++
      Lines.section("Its code calls (proven from their promises alone)", d.calls.map(Lines.node(_, st)), st) ++
      Lines.section("Called by the code of", d.calledBy.map(Lines.node(_, st)), st) ++
      Lines.section("Vocabulary", d.terms.flatMap(t => Lines.para(s"${t.name}${if t.operation then " (operation)" else ""}: ${t.means} " +
        t.definedBy.fold("(open)")(x => s"(defined by $x)"), st)), st) ++
      Lines.section("Proofs", proofs(d, st), st) ++
      Lines.section(examplesTitle(n), examples(n, st), st) ++
      Lines.section("Code", code(d, st), st) ++
      Lines.section("Messages from the last check", n.messages.flatMap(_.linesIterator), st) ++
      Lines.section("Decisions", r.review.history.flatMap(h => Lines.para(s"${Words.date(h.at)}  ${Words.verb(h.action)} by ${h.by}: ${h.reason}", st)), st) ++
      Lines.section("Alternatives rejected for it", r.review.alternatives.map(a => s"${a.id}: ${a.content.statement}"), st) ++
      Lines.section("Requests", d.requests.flatMap(q => s"[${q.id}] ${q.status} ${st.dot} ${q.by}: ${q.text}" ::
        q.answer.filter(_.nonEmpty).map(a => s"  agent: $a").toList), st) ++
      (if lean then leanText(n, st) else Nil)

  private def header(d: NodeDetails, st: Style): List[String] =
    val r = d.node
    val n = r.node
    val kind = n.shownKind + n.op.fold("")(o => s" on $o") + (if d.isRoot then " (the root)" else "")
    val state = Lines.state(r)
    val marks = List(Option.when(d.trusted)(st.yellow("trusted")), Option.when(d.withAgent)(st.magenta("asked of the agent")),
      n.replaces.map(x => st.dim(s"replaces $x"))).flatten
    val room = st.width.fold(Int.MaxValue)(_ - 2)
    s"${st.glyph(Glyph.of(r))} ${st.bold(r.id.value)}  ${st.dim(kind)}  ${st.state(r.state, state)}${marks.map("  " + _).mkString}" ::
      st.wrap(n.content.statement, room).map("  " + _) ++
      st.wrap(s"why: ${n.content.why}", room).map(l => "  " + st.dim(l))

  /** What deciding it acts on: what it waits for, whether it is mechanical, what is not proven, the
    * rivals it rejects, the decisions below, the options rejected before.
    */
  private def decision(d: NodeDetails, st: Style): List[String] =
    val r = d.node
    val v = r.review
    val open = r.state == ReviewState.Proposed || r.state == ReviewState.Review
    val lines = if !open then Nil else
      Option.when(r.state == ReviewState.Review)(st.yellow(s"to review: ${v.causes.flatMap(Words.causes.get).mkString("; ")}")).toList ++
      v.waitsFor.map(w => st.yellow(s"decide $w first: what rests on it is decided after it")).toList ++
        (if v.mechanical then List(st.green("mechanical: Lean proves it again and nothing in it is a choice (confirm decides the batch)"))
         else v.notMechanical.filter(_ => r.state == ReviewState.Review).map(st.dim).toList) ++
        v.unproven.map(u => st.red(s"note: $u")) ++
        Option.when(d.rivals.exists(_.state != ReviewState.Rejected))(
          s"accepting it rejects ${d.rivals.filter(_.state != ReviewState.Rejected).map(_.id).mkString(", ")} (its alternatives), with your reason").toList ++
        v.rejectedBeside.filter(_ => r.state == ReviewState.Proposed).map(x => st.dim(s"rejected here before: ${x.id}: ${x.statement} — because ${x.reason}")) ++
        (if v.below.isEmpty then Nil else
          "decisions below it, with their reasons (accept --revisit NODE reviews one again; one that moved only with it is confirmed):" ::
            v.below.flatMap(b => Lines.para(s"${b.id}${if b.kind == BelowKind.Moved then " (moved with it)" else ""}: ${b.statement} " +
              s"— holds because: ${b.reason}", st, indent = 4).map("  " + _)))
    val chosen = v.reasonNow.filter(_ => r.state == ReviewState.Accepted).toList.flatMap(x => Lines.para(s"holds because: $x", st))
    val rejected = Option.when(r.state == ReviewState.Rejected)(r.review.history.reverse.find(_.action == Action.Reject)).flatten
      .map(h => st.red(s"rejected by ${h.by}: ${h.reason} (the agent removes it, or proposes what the reason asks for)")).toList
    Lines.section("Decision", lines ++ chosen ++ rejected, st)

  private def formal(n: SnapNode): List[String] =
    val sources = n.content("sources").flatMap(_.asObject).fold(Nil)(_.toList.flatMap((k, v) => v.asString.map(k -> _)))
    sources.flatMap((k, src) => s"$k${if k == "post" then n.op.fold("")(o => s" (every call of $o)") else ""}:" :: src.linesIterator.map("  " + _).toList) ++
      n.content.strs("substitutions").map("  " + _) ++
      n.invariants.flatMap(i => if i.status == ObligationStatus.Exempt then List(s"exempt from ${i.id}: ${i.detail}")
        else s"keeps ${i.id} (${i.status}), showing the rule:" :: i.view.linesIterator.map("  " + _).toList) ++
      Option.when(n.covers.nonEmpty)(s"kept by ${n.covers.mkString(", ")}").toList ++
      Option.when(n.exempts.nonEmpty)(s"exempt: ${n.exempts.mkString(", ")}").toList ++
      n.expectations.flatMap(e => s"expects (${e.status}): ${e.statement}" :: e.source.linesIterator.map("  " + _).toList)

  /** How it serves a parent: needed there or not, and with which co-parts. */
  private def partOf(p: Reviewed, r: Reviewed, st: Style): String =
    val need = p.node.split.flatMap(_.needed.find(_.id == r.id))
    val co = p.node.parts.filter(_ != r.id)
    st.dim(s" — ${if co.isEmpty then "its only part" else s"with ${co.mkString(", ")}, together they make it"}") +
      need.filter(_.status == ObligationStatus.Shown).fold("")(x => st.red(s"; not needed: ${x.detail}"))

  private def parts(d: NodeDetails, st: Style): List[String] =
    val sp = d.node.node.split
    d.parts.map { p =>
      val need = sp.flatMap(_.needed.find(_.id == p.id))
      Lines.node(p, st, extra = need.fold("")(x => "  " + (if x.status == ObligationStatus.Shown then st.red(s"not needed: ${x.detail}") else st.dim("needed"))))
    } ++ sp.map(s => s"clash: ${outcome(s.clash, st)}").toList

  def outcome(o: Outcome, st: Style): String =
    val text = s"${o.status}${if o.detail.isEmpty then "" else s": ${o.detail.linesIterator.nextOption().getOrElse("")}"}"
    if o.status.fine then st.green(text)
    else if o.status == ObligationStatus.Unchecked then st.dim(text)
    else st.red(text)

  /** Every obligation and try with its status, in honest words. */
  private def proofs(d: NodeDetails, st: Style): List[String] =
    val n = d.node.node
    val split = n.split.toList.flatMap(sp => s"complete: ${outcome(sp.complete, st)}" ::
      sp.needed.map(p => s"needed ${p.id}: ${outcome(Outcome(p.status, p.detail), st)}"))
    split ++ n.implementationProof.map(p => s"impl (${p.name}): ${outcome(Outcome(p.status, p.detail), st)}") ++
      n.rootImpl.map(o => s"root_impl: ${outcome(o, st)}") ++
      n.idle.map(i => st.red(s"idle: Lean shows doing nothing meets it ($i): say what users can do")) ++
      n.status.filter(_ != CheckStatus.Proven).map(s => st.yellow(s"check: $s"))

  private def examplesTitle(n: SnapNode): String =
    val (ok, total) = n.examplesPassing
    val lean = n.examples.flatMap(_.lean)
    s"Examples: $ok of $total pass" + (if lean.isEmpty then "" else s"; Lean agrees on ${lean.count(_.status == ObligationStatus.Proven)} of ${lean.size}")

  /** The examples under the values they are given, each group once. */
  private def examples(n: SnapNode, st: Style): List[String] =
    n.examples.foldLeft((List.empty[String], Option.empty[List[String]])) { case ((done, last), e) =>
      val head = Option.when(!last.contains(e.`given`))(st.dim(s"given ${if e.`given`.isEmpty then "nothing" else e.`given`.mkString(", ")}")).toList
      (done ++ head :+ ("  " + example(e, st)), Some(e.`given`))
    }._1

  private def example(e: ExampleView, st: Style): String =
    val mark = if e.passes then st.glyph(Glyph.Proven) else st.glyph(Glyph.Failed)
    val verdict = if e.passes then "" else st.red(s"  contract: ${e.fails.getOrElse("ok")}${e.codeFails.fold("")(i => s", implementation: $i")}")
    val lean = e.lean.fold("")(o => if o.status == ObligationStatus.Proven then st.dim("  Lean agrees")
      else if o.status == ObligationStatus.Failed then st.red(s"  Lean disagrees: ${o.detail}") else st.dim(s"  ${o.status} in Lean"))
    s"$mark ${if e.expected then "expect" else "reject"} ${e.call}  ${st.dim(s"— ${e.note}")}$verdict$lean"

  private def code(d: NodeDetails, st: Style): List[String] =
    val n = d.node.node
    val impl = n.content.text("implementation")
    def runs(r: Option[String]) = r.fold("")(c => s"; running code $c checked against it")
    val how = CodeProof.of(n).map {
      case CodeProof.ProvenDown(define, running) => s"proven define $define${runs(running)}"
      case CodeProof.Define(define, status, running) => s"define $define, $status${runs(running)}"
      case CodeProof.ByRunning => "checked by running: a plain implementation, not proven"
    }
    how.toList ++ Option.when(impl.nonEmpty)(impl.linesIterator.map(l => st.dim("  " + l)).toList).toList.flatten ++
      n.code.map(c => s"governs: ${c.files.mkString(", ")}" +
        (if d.diff.code.exists(_.inFull) then st.yellow(s"  (diff ${d.node.id} shows them in full: read them before accepting)") else ""))

  private def leanText(n: SnapNode, st: Style): List[String] =
    Lines.section("Theorem holds (from the leaves below it)", n.holds.linesIterator.toList, st) ++
      Lines.section("Obligations in Lean", n.obligations.flatMap(o => s"${st.bold(o.name)}: ${o.description}" :: o.statement.linesIterator.map("  " + _).toList), st) ++
      Lines.section(n.proof.fold("Proof file")(p => s"Proof file ${p.file}"), n.proof.toList.flatMap(_.source.linesIterator), st) ++
      Lines.section("Generated Lean", n.lean.linesIterator.toList, st)
