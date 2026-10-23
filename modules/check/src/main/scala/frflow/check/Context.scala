package frflow
package check

import frflow.ledger.Idea
import frflow.protocol.*

/** Everything known about a node (docs/DAG.md §7): its idea section, the vocabulary it uses (terms,
  * meanings, definitions in force), the nodes above it with their reasons, the co-parts under each
  * parent, its parts, the alternatives rejected, what moved, and what the developer asked for. This is
  * what a fresh agent, or a new engineer, reads first: Markdown, in sections.
  */
final case class Context(title: String, sections: List[Context.Section]):
  def text: String = s"# $title\n\n" + sections.map(s => s"## ${s.heading}\n\n${s.body}").mkString + Context.Footer

object Context:
  /** A section: its heading, and its body in Markdown. */
  final case class Section(heading: String, body: String)

  val Footer: String =
    "A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.\n" +
      "The developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).\n"

  /** The context of `n`, given the developer's requests and, when its code moved, how (a git diff, or ""). */
  def of(a: Analysis, n: Node[?], requests: List[Request], codeDiff: String): Context =
    val c = Ctx(a, n)
    Context(s"${a.kb.name} / ${n.id}", List(
      Some(c.idea), Some(c.vocabulary), c.above, Some(Section("The node", c.show(n)))).flatten ++
      c.beside ++ c.parts ++ c.calls ++ c.users ++ c.invariants ++ c.moved(codeDiff) ++ c.obligations ++ c.lastCheck ++
      c.requests(requests))

  private final case class Ctx(a: Analysis, n: Node[?]):
    private val kb = a.kb
    private val g = a.generate
    private val l = a.ledger
    private val st: Map[String, ReviewState] = a.annotated.nodes.map(r => r.id.value -> r.state).toMap
    private def state(x: Node[?]) = st.get(x.id).fold("?")(_.toString)
    private def kind(x: Node[?]) = x.shownKind
    private def id(x: Node[?]) = NodeId(x.id)
    private def lines(xs: List[String]): String = xs.map(_ + "\n").mkString
    private def code(label: String, lang: String, src: String) = s"$label```$lang\n$src\n```\n"

    def idea: Section =
      val section = (n :: kb.ancestors(n)).find(_.ideaSection.trim.nonEmpty)
      val text = Idea.sections(a.ideaDecided)._1 + section.fold("")(s => "\n\n" + a.ideaOf(s)) +
        (if a.notModelled.nonEmpty then s"\n\n## Not modelled\n\n${a.notModelled}" else "")
      Section(s"Idea (${section.fold("its purpose")(s => s"the section ${s.ideaSection}")})", s"${text.trim}\n\n")

    // What its terms mean: the open terms, and the definitions in force (as decided).
    def vocabulary: Section =
      val used = kb.definitionsUsed(n, g.inForce)
      val defs = Def.closure((n :: used).flatMap(_.referenced).flatMap(_.defs))
      Section("Vocabulary it uses", lines(Contents.vocabulary(kb, n).map(v => s"- $v")) +
        lines(used.map(d => s"- defined by ${d.id} [${state(d)}]: ${d.statement} ${d.substs.map(s => s"`${s.name} := ${s.term.fold(s.lean)(_.source)}`").mkString(", ")}")) +
        defs.map(d => code("", "scala", s"${d.name} = ${d.lifted.source}")).mkString + "\n")

    // The nodes above, nearest first, each once.
    def above: Option[Section] =
      val up = kb.ancestors(n)
      Option.when(up.nonEmpty)(Section("Above it (what it helps prove), nearest first", up.map(show).mkString))

    /** Every decision on a node, oldest first, each marked if given for an earlier version of what it says. */
    private def reasons(x: Node[?]): String =
      val now = a.hash(x)
      def ver(d: Decision) = if d.hash == now || !d.action.binds then "" else " [given for an earlier version of it]"
      def line(d: Decision) = d.action match
        case Action.Accept if l.chosen(id(x)).contains(d) => s"Chosen by ${d.by} because: ${d.reason}"
        case Action.Accept  => s"Change accepted by ${d.by}: ${d.reason}"
        case Action.Confirm => s"Confirmed by ${d.by}: ${d.reason}"
        case Action.Revisit => s"To revisit (${d.by}): ${d.reason}"
        case Action.Reject  => s"Rejected by ${d.by} at ${d.at}: ${d.reason}"
        case other          => s"${other.toString.capitalize} by ${d.by}: ${d.reason}"
      l.history(id(x)).map(d => s"${line(d)}${ver(d)}\n\n").mkString +
        lines(l.alternatives(id(x)).map((alt, c) => s"- Rejected alternative $alt: ${c.statement} (why: ${c.why})"))

    def show(x: Node[?]): String =
      s"### ${x.id} (${kind(x)}) [${state(x)}]\n\n${x.statement}\n\nWhy: ${x.why}\n\n" + reasons(x) +
        x.formula.map(f => code("formula:\n", "scala", f.source)).mkString +
        x.post.map(p => code(s"post (of every call of ${x.op.fold("")(_.name)}):\n", "scala", p.source)).mkString +
        x.rule.map(r => code("rule:\n", "scala", r.source)).mkString +
        lines(x.substs.map(s => s"- `${s.name} := ${s.term.fold(s.lean)(_.source)}`") ++
          (if kb.isRoot(x) then a.idleOf(x).map(w => s"- doing nothing meets it ($w): it says only what must not happen; state what users can do").toList else Nil) ++
          a.examples(x).map(r => s"- example: ${r.example.describe} [${r.verdict}]") ++
          a.code(x).map(c => s"- governs: ${c.files.mkString(", ")}")) +
        a.content(x).str("implementation").map(i => code("implementation:\n", "scala", i)).mkString + "\n"

    // Under each parent: the other parts, which together with this one make it, and those rejected there.
    def beside: List[Section] = kb.parentsOf(n).flatMap { p =>
      val others = kb.parts(p).filterNot(_ eq n)
      val rejected = l.rejectedUnder(id(p)).filterNot((r, _, _) => r == id(n) || others.exists(b => id(b) == r))
      Option.when(others.nonEmpty || rejected.nonEmpty)(Section(s"Beside it, under ${p.id} (its co-parts: together they make ${p.id})",
        lines(others.map(o => s"- ${o.id} (${kind(o)}) [${state(o)}]: ${o.statement}") ++
          rejected.map((r, c, why) => s"- rejected $r: ${c.statement} — rejected because: $why")) + "\n"))
    }

    def parts: Option[Section] =
      val ps = kb.children(n)
      Option.when(ps.nonEmpty)(Section("Its parts (a change here may affect them)", ps.map { c =>
        s"- ${c.id} (${kind(c)}) [${state(c)}]: ${c.statement} Why: ${c.why}\n" + l.chosen(id(c)).fold("")(d => s"  Chosen by ${d.by} because: ${d.reason}\n")
      }.mkString + "\n"))

    // The contracts its code calls: proven from their promise alone.
    def calls: Option[Section] =
      val cs = g.callees(n)
      Option.when(cs.nonEmpty)(Section("Its code calls", cs.map { o =>
        s"### ${o.id} (${kind(o)}) [${state(o)}]\n\nIts code calls ${o.op.fold("")(_.name)}, and is proven from this promise alone (not from its code):\n\n${o.statement}\n\n" +
          o.post.map(x => s"```scala\n${x.source}\n```\n\n").mkString
      }.mkString))

    def users: Option[Section] =
      val us = kb.nodes.filter(c => !(c eq n) && a.restsOn(c).exists(_ eq n) && !kb.parentsOf(c).exists(_ eq n))
      Option.when(us.nonEmpty)(Section("Rests on it besides its parts (a change to its meaning puts them up for review)",
        lines(us.map(c => s"- ${c.id} [${state(c)}]: ${c.statement}")) + "\n"))

    // The cross-cutting rules that reach this node: every contract in their scope keeps them or is exempt.
    def invariants: Option[Section] =
      val invs = kb.nodes.filter(i => i.isInvariant && ((i eq n) || i.scope.isEmpty || (n :: kb.ancestors(n)).exists(x => i.scope.exists(_ eq x))))
      Option.when(invs.nonEmpty)(Section("Invariants that apply here (every contract in their scope keeps them, or says why not)", invs.map { i =>
        s"### ${i.id} (invariant) [${state(i)}]\n\n${i.statement}\n\nWhy: ${i.why}\n\n" + i.rule.map(r => code("rule:\n", "scala", r.source)).mkString +
          lines(kb.nodes.flatMap(c => c.kept.filter(_.invariant eq i).map(c -> _)).map((c, k) =>
            k.view.fold(s"- ${c.id} is exempt: ${k.exempt}")(v => s"- kept by ${c.id}, showing the rule: `${v.source}`"))) + "\n"
      }.mkString))

    /** The causes of its review, if any. */
    def causes: List[Cause] = a.annotated.byId.get(id(n)).fold(Nil)(_.review.causes)

    def moved(codeDiff: String): Option[Section] = a.annotated.byId.get(id(n)).filter(_.review.causes.nonEmpty).map { me =>
      val cs = me.review.causes
      def fields(before: Content, now: Content): String =
        def flat(c: Content): Map[String, String] = c.fields.map((k, v) =>
          k -> v.asString.orElse(v.asArray.map(_.map(x => x.asString.getOrElse(Canonical.print(x))).mkString("\n"))).getOrElse(Canonical.print(v))).toMap
        val (b, now2) = (flat(before), flat(now))
        def indent(t: String) = t.linesIterator.mkString("\n      ")
        (b.keySet ++ now2.keySet).toList.sorted.filter(k => b.get(k) != now2.get(k)).map { k =>
          s"  - $k\n    was: ${indent(b.getOrElse(k, ""))}\n    now: ${indent(now2.getOrElse(k, ""))}\n"
        }.mkString
      val self = if cs.contains(Cause.Self) then l.binding(id(n)).map(d => s"- ${n.id} itself changed:\n${fields(d.content, me.node.content)}").mkString else ""
      val meaning = me.review.moved.map(m => s"- the meaning of ${m.id} changed:\n${fields(m.before, a.annotated.byId.get(m.id).fold(Content.empty)(_.node.content))}").mkString
      val rejected = kb.parentsOf(n).filter(p => st.get(p.id).contains(ReviewState.Rejected)).map(p => s"- its parent ${p.id} was rejected: move it under the node chosen instead\n").mkString
      val revisit = if cs.contains(Cause.Revisit) then l.current(id(n)).filter(_.action == Action.Revisit).map(r => s"- ${r.by} asked to revisit it: ${r.reason}\n").mkString else ""
      val code = if !cs.contains(Cause.Code) then ""
        else if codeDiff.nonEmpty then s"- the code it governs changed:\n```diff\n$codeDiff```\n" else "- the code it governs changed (no git diff available)\n"
      Section(s"What moved since ${n.id} was decided: ${cs.mkString(", ")}", self + meaning + rejected + revisit + code + "\n")
    }

    def obligations: List[Section] = g.obligations(n).map { o =>
      val stl = a.current(n).flatMap(_.result(o.name)).fold("not checked")(r => s"${r.status}${r.detail.linesIterator.nextOption().fold("")(d => s" ($d)")}")
      Section(s"Obligation ${o.name} of ${n.id} [$stl]", s"${o.description}\n\n```lean\n${o.statement}\n```\n\n")
    }

    // What the last check left open or failed, with Lean's message in full (the goal it stopped at).
    def lastCheck: Option[Section] = a.current(n).orElse(a.checks.get(id(n))).flatMap { c =>
      val bad = c.obligations.filter(!_.fine)
      Option.when(bad.nonEmpty || c.messages.nonEmpty)(Section(
        s"Last check of ${n.id}: ${c.status}${if a.current(n).isEmpty then " (before the latest change)" else ""}",
        bad.map(r => s"- ${r.status} ${r.name}:\n```\n${r.detail}\n```\n").mkString + lines(c.messages.map(m => s"- $m")) + "\n"))
    }

    def requests(all: List[Request]): Option[Section] =
      val asks = all.filter(_.node.contains(id(n)))
      Option.when(asks.nonEmpty)(Section("Requests from the developer",
        lines(asks.map(r => s"- [${r.id}, ${r.status}] ${r.text}${r.answer.filter(_.nonEmpty).fold("")(x => s"\n  Answer: $x")}")) + "\n"))
