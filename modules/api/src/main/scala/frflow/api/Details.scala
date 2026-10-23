package frflow.api

import frflow.protocol.*

/** A node with what surrounds it, and what changed since it was decided: what `show`, `diff` and the
  * review read.
  */
object Details:
  def of(v: View, r: Reviewed, code: Option[CodeChange]): NodeDetails =
    val (designs, parts) = r.node.parts.flatMap(v.node).partition(_.node.kind == NodeKind.Design)
    NodeDetails(
      node = r,
      isRoot = v.isRoot(r),
      trusted = v.snapshot.trusted.contains(r.id),
      parents = r.node.parents.flatMap(v.node),
      parts = parts,
      designs = designs,
      definitions = r.node.uses.flatMap(v.node),
      usedBy = v.nodes.filter(_.node.uses.contains(r.id)),
      calls = r.node.relies.flatMap(v.node),
      calledBy = v.nodes.filter(_.node.relies.contains(r.id)),
      rivals = r.review.rivals.flatMap(v.node),
      terms = terms(v, r),
      requests = v.requests.filter(q => q.node.contains(r.id) && q.status != RequestStatus.Closed),
      withAgent = v.withAgent(r),
      diff = diff(v, r, code))

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

  /** The decision a node is bound to now: its last acceptance or confirmation, unless it was rejected since. */
  def binding(r: Reviewed): Option[Decision] =
    r.review.history.lastOption.filter(d => d.action != Action.Reject && d.action != Action.Remove)
      .flatMap(_ => r.review.history.reverse.find(_.action.binds))

  /** What changed since the node was decided, by cause; `code` is how its code changed (or, never decided, the code in full). */
  def diff(v: View, r: Reviewed, code: Option[CodeChange]): NodeDiff =
    val causes = r.review.causes
    val since = binding(r)
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
      rejectedParents = if causes.contains(Cause.Above) then Queue.rejectedParents(v, r) else Nil,
      revisit = Option.when(causes.contains(Cause.Revisit))(r.review.history.reverse.find(_.action == Action.Revisit)).flatten,
      code = code,
      statementStale = changedFields.exists(Fields.formal) && !changedFields("statement"))
