package frflow.api
package details

import frflow.ledger.{CodeProof, Graph, Waiting}
import frflow.protocol.*

object Details:
  /** The node, if it is gone from the model. */
  def gone(v: View, id: NodeId): Option[GoneNode] = v.annotated.gone.find(_.id == id).map(gone(v, _))
  def gone(v: View, g: Gone): GoneNode =
    def said(s: String) = s.replaceAll("\\s+", " ").trim
    val statement = said(g.decision.content.statement)
    GoneNode(g, v.nodes.find(r => statement.nonEmpty && said(r.node.content.statement) == statement).map(_.id))

  def of(v: View, r: Reviewed, code: Option[CodeChange]): NodeDetails =
    val (premises, below) = r.node.parts.flatMap(v.node).partition(x => r.node.premises.contains(x.id))
    val (designs, parts) = below.partition(_.node.kind == NodeKind.Design)
    val parents = r.node.parents.flatMap(v.node)
    // Nearest first (see `Graph.ancestry`): their reasons say when to revisit them.
    val above = Graph(v.snapshot).ancestry(r.node).filter(_ != r.id).flatMap(v.node)
    val tested = v.snapshot.tested.contains(r.id)
    NodeDetails(r, v.isRoot(r), v.snapshot.trusted.contains(r.id) && !tested, idea(v, r, above), parents,
      parents.map(p => p.id -> p.node.parts.filter(_ != r.id).flatMap(v.node)), above, parts, designs,
      r.node.uses.flatMap(v.node), v.nodes.filter(_.node.uses.contains(r.id)), r.node.relies.flatMap(v.node),
      v.nodes.filter(_.node.relies.contains(r.id)), v.nodes.filter(_.node.invariants.exists(_.id == r.id)),
      r.review.rivals.flatMap(v.node), terms(v, r), defs(v, r), CodeProof.of(r.node), diff(v, r, code), premises, tested)

  /** The root's idea (its lead), the section of the nearest node naming one, and what is not modelled. */
  private def idea(v: View, r: Reviewed, up: List[Reviewed]): String =
    def text(x: Reviewed) = x.node.content.text("idea")
    val section = (r :: up).find(text(_).nonEmpty)
    val root = v.snapshot.root.flatMap(v.node)
    val lead = root.filterNot(x => section.exists(_.id == x.id)).map(text)
    val notModelled = section.orElse(root).map(_.node.content.text("notModelled")).filter(_.nonEmpty).map("Not modelled:\n" + _)
    (lead.toList ++ section.map(text) ++ notModelled).map(_.trim).filter(_.nonEmpty).mkString("\n\n")

  /** Its `vocabulary` lines read "name: means". */
  private def terms(v: View, r: Reviewed): List[Term] =
    val opaques = v.snapshot.opaques.map(o => o.name -> o.definedBy).toMap
    val params = v.snapshot.params.map(p => p.name -> p).toMap
    r.node.content.strs("vocabulary").map { line =>
      val (name, means) = line.span(_ != ':') match { case (n, m) => (n.trim, m.drop(1).trim) }
      Term(name, means, params.get(name).exists(_.operation), params.get(name).flatMap(_.definedBy).orElse(opaques.get(name).flatten))
    }

  private def defs(v: View, r: Reviewed): List[DefText] =
    def named(text: String) = v.snapshot.defs.filter(d => s"\\b${java.util.regex.Pattern.quote(d.name)}\\b".r.findFirstIn(text).isDefined)
    val sources = r.node.content("sources").flatMap(_.asObject).fold(Nil)(_.values.flatMap(_.asString).toList)
    Walk.preorder(sources.flatMap(named), (d: DefText) => d.name)(d => named(d.source).filter(_.name != d.name))

  def diff(v: View, r: Reviewed, code: Option[CodeChange]): NodeDiff =
    val causes = r.review.causes
    val since = r.review.binding
    val self = since.filter(_ => causes.contains(Cause.Self)).fold(Nil)(d => Fields.changes(d.content, r.node.content))
    val (added, removed) = since.filter(_ => causes.contains(Cause.Parts)).flatMap(_.content.parts).fold((Nil, Nil)) { before =>
      (r.node.parts.filterNot(before.contains), before.filterNot(r.node.parts.contains))
    }
    val moved = r.review.moved.map { m =>
      val now = v.node(m.id)
      MovedAbove(m.id, now.exists(_.state == ReviewState.Accepted), now.flatMap(_.review.reasonNow),
        Fields.changes(m.before, now.fold(Content.empty)(_.node.content)))
    }
    val changed = self.map(_.field).toSet
    NodeDiff(r.id, causes, since, self, added, removed, moved,
      if causes.contains(Cause.Above) then Waiting.rejectedParents(v.annotated, r) else Nil,
      Option.when(causes.contains(Cause.Revisit))(r.review.history.reverse.find(_.action == Action.Revisit)).flatten,
      code, changed.exists(Fields.formal) && !changed("statement"))
