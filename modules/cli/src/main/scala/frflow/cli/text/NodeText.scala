package frflow.cli.text

import frflow.api.node.{NodeView, Relation}
import frflow.api.view.{View, Views}
import frflow.cli.say.{Refusals, Unprovens}
import frflow.cli.term.{Marks, Style}
import frflow.core.name.NodeId
import frflow.decision.review.ReviewState

/** A node as `show` and the review print it: its header, what deciding it takes, why it holds, what it says formally
  * and how that is checked, where it sits, its proofs and code, and what layers on top add (`layers`).
  */
final class NodeText(v: View, style: Style, layers: Contribution):
  def lines(n: NodeView, depth: Depth): List[String] =
    val full = depth == Depth.Full
    val normal = depth != Depth.Brief
    val st = if full then style.copy(width = None) else style
    val sections: List[(Boolean, String, List[String])] = List(
      (true, "Decision", decision(v, n, st)),
      (true, "Why it holds (the reason it was decided with)", reason(n)),
      (true, "Formally (as written in Scala)", n.says.written.toList.flatMap(_.linesIterator.map(l => st.dim(l)))),
      (normal, "How it is checked", n.says.checking),
      (normal, "Where it sits", place(v, n, st)),
      (true, "Parts: together, with the assumptions it lists, they make it",
        n.place(Relation.Part).map(Lines.of(v, _, st, 2))),
      (true, "Rules it uses (no part of its step: Lean has each of every value)", rules(n, st)),
      (full, "What it mentions", mentions(n))) ++
      Views.beside(v, n.id).map((p, co) => (full, s"Beside it under $p: together they make $p",
        co.map(Lines.of(v, _, st, 2)))) ++ ProofText.sections(n, st, full).map((t, ls) => (normal, t, ls))
    (header(n, st, layers.marks.get(n.id)) ++ sections.flatMap((shown, title, ls) =>
      if shown then Lines.section(title, ls, st) else Nil) ++ (if normal then layers.node(n.id) else Nil))
      .flatMap(st.fold(_))

  private def header(n: NodeView, st: Style, mark: Option[String]): List[String] =
    val kind = Lines.kind(n.says.kind) + (if n.place.root then " (a root)" else "")
    val state = n.review.standing.state
    s"${Marks.glyph(n, st)} ${st.bold(n.id.value)}  ${st.dim(kind)}  ${Marks.state(state, Refusals.state(state), st)}" +
      mark.fold("")(m => "  " + st.magenta(m)) :: st.width.fold(List(Lines.statement(n)))(w =>
        st.wrap(Lines.statement(n), w - 2)).map("  " + _)

  /** What deciding it takes: why it is back, what it waits for, whether `confirm` takes it, what is not proven, the
    * rivals accepting it rejects, and the decisions below that accepting it acts on.
    */
  private def decision(v: View, n: NodeView, st: Style): List[String] =
    val r = n.review
    val open = r.standing.state == ReviewState.Proposed || r.standing.state == ReviewState.Review
    val rivals = n.place(Relation.Rival).filter(x => v.node(x).exists(_.review.standing.state != ReviewState.Rejected))
    if !open then Nil
    else Option.when(r.standing.state == ReviewState.Review)(st.yellow(
        s"to review: ${r.standing.causes.map(Unprovens.cause).mkString("; ")}")).toList ++
      r.waitsFor.map(w => st.yellow(s"decide $w first: what rests on it is decided after it")).toList ++
      mechanical(n, st).toList ++ n.proof.unproven.map(u => st.red(s"note: ${Unprovens.text(u)}")) ++
      Option.when(rivals.nonEmpty)(s"accepting it rejects ${rivals.mkString(", ")}, with your reason").toList ++
      r.moves.above.map(m => st.dim(s"moved above it since it was decided: $m (diff ${n.id} shows how)")) ++
      below(r.moves.below)

  private def mechanical(n: NodeView, st: Style): Option[String] =
    if InboxText.mechanical(n) then
      Some(st.green("mechanical: Lean proves it again and nothing in it is a choice (confirm takes the batch)"))
    else n.review.notMechanical.filter(_ => n.review.standing.state == ReviewState.Review && n.review.waitsFor.isEmpty)
      .map(x => st.dim(s"not mechanical: ${Unprovens.notMechanical(x)}"))

  private def below(ids: List[NodeId]): List[String] =
    if ids.isEmpty then Nil
    else List("decisions below it that accepting it acts on (accept --revisit NODE reviews one again): " +
      ids.mkString(", "))

  private def reason(n: NodeView): List[String] = n.review.decisions.binding.map(d =>
    s"${d.reason.text}  (${Unprovens.verb(d.action)} by ${d.author.by}, ${d.author.at.toString.take(16)
      .replace('T', ' ')})").toList

  private def place(v: View, n: NodeView, st: Style): List[String] =
    val rows = List(Relation.Parent -> "part of", Relation.Assumes -> "assumes", Relation.AssumedBy -> "assumed by",
      Relation.Design -> "design", Relation.Calls -> "calls", Relation.CalledBy -> "called by",
      Relation.Rival -> "rival")
    rows.flatMap((rel, label) => n.place(rel).map(id => label.padTo(11, ' ') + Lines.of(v, id, st, 13)))

  /** Each rule it uses, said of whether it takes it: a hypothesis on a value or a world it is about. */
  private def rules(n: NodeView, st: Style): List[String] =
    n.place(Relation.Rule).map(Lines.of(v, _, st, 2)) ++
      n.place(Relation.UnusedRule).map(id => Lines.of(v, id, st, 2) + st.dim("  (not taken: it is about nothing here)"))

  private def mentions(n: NodeView): List[String] =
    val m = n.says.mentions
    List("values" -> m.symbols.map(_.value), "defines" -> m.defines.map(_.value), "types" -> m.types.map(_.value),
      "stores" -> m.models.map(_.value)).collect { case (k, xs) if xs.nonEmpty => s"$k: ${xs.mkString(", ")}" }
