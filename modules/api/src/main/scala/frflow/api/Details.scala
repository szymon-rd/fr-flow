package frflow.api

import frflow.ledger.{CodeProof, Graph, Waiting}
import frflow.protocol.*

/** A node with what surrounds it, and what changed since it was decided: what `show`, `diff` and the
  * review read.
  */
object Details:
  def of(v: View, r: Reviewed, code: Option[CodeChange]): NodeDetails =
    val (designs, parts) = r.node.parts.flatMap(v.node).partition(_.node.kind == NodeKind.Design)
    val parents = r.node.parents.flatMap(v.node)
    val up = above(v, r)
    NodeDetails(
      node = r,
      isRoot = v.isRoot(r),
      trusted = v.snapshot.trusted.contains(r.id),
      idea = idea(v, r, up),
      parents = parents,
      beside = parents.map(p => p.id -> p.node.parts.filter(_ != r.id).flatMap(v.node)),
      above = up,
      parts = parts,
      designs = designs,
      definitions = r.node.uses.flatMap(v.node),
      usedBy = v.nodes.filter(_.node.uses.contains(r.id)),
      calls = r.node.relies.flatMap(v.node),
      calledBy = v.nodes.filter(_.node.relies.contains(r.id)),
      keptBy = v.nodes.filter(_.node.invariants.exists(_.id == r.id)),
      rivals = r.review.rivals.flatMap(v.node),
      terms = terms(v, r),
      defs = defs(v, r),
      codeProof = CodeProof.of(r.node),
      requests = v.requests.filter(q => q.node.contains(r.id) && q.status != RequestStatus.Closed),
      withAgent = v.withAgent(r),
      diff = diff(v, r, code))

  /** What a node rests on, nearest first (see `Graph.ancestry`): their reasons say when to revisit them. */
  def above(v: View, r: Reviewed): List[Reviewed] = Graph(v.snapshot).ancestry(r.node).filter(_ != r.id).flatMap(v.node)

  /** The root's idea (its lead), the section of the nearest node naming one, and what is not modelled. */
  private def idea(v: View, r: Reviewed, up: List[Reviewed]): String =
    def text(x: Reviewed) = x.node.content.text("idea")
    val section = (r :: up).find(text(_).nonEmpty)
    val root = v.snapshot.root.flatMap(v.node)
    val lead = root.filterNot(x => section.exists(_.id == x.id)).map(text)
    val notModelled = section.orElse(root).map(_.node.content.text("notModelled")).filter(_.nonEmpty).map("Not modelled:\n" + _)
    (lead.toList ++ section.map(text) ++ notModelled).map(_.trim).filter(_.nonEmpty).mkString("\n\n")

  /** The terms a node mentions (its `vocabulary`, "name: means"), with the definition fixing each. */
  def terms(v: View, r: Reviewed): List[Term] =
    val opaques = v.snapshot.opaques.map(o => o.name -> o.definedBy).toMap
    val params = v.snapshot.params.map(p => p.name -> p).toMap
    r.node.content.strs("vocabulary").map { line =>
      val (name, means) = line.indexOf(':') match
        case -1 => (line.trim, "")
        case i => (line.take(i).trim, line.drop(i + 1).trim)
      Term(name, means, params.get(name).exists(_.operation), params.get(name).flatMap(_.definedBy).orElse(opaques.get(name).flatten))
    }

  /** The functions its formal statement names, and those they name in turn. */
  private def defs(v: View, r: Reviewed): List[DefText] =
    def named(text: String) = v.snapshot.defs.filter(d => s"\\b${java.util.regex.Pattern.quote(d.name)}\\b".r.findFirstIn(text).isDefined)
    val sources = r.node.content("sources").flatMap(_.asObject).fold(Nil)(_.values.flatMap(_.asString).toList)
    Walk.preorder(sources.flatMap(named), (d: DefText) => d.name)(d => named(d.source).filter(_.name != d.name))

  /** What changed since the node was decided, by cause; `code` is how its code changed (or, never decided, the code in full). */
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
    val changedFields = self.map(_.field).toSet
    NodeDiff(
      id = r.id,
      causes = causes,
      since = since,
      self = self,
      partsAdded = added,
      partsRemoved = removed,
      moved = moved,
      rejectedParents = if causes.contains(Cause.Above) then Waiting.rejectedParents(v.annotated, r) else Nil,
      revisit = Option.when(causes.contains(Cause.Revisit))(r.review.history.reverse.find(_.action == Action.Revisit)).flatten,
      code = code,
      statementStale = changedFields.exists(Fields.formal) && !changedFields("statement"))
