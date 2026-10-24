package frflow.api

import frflow.ledger.{CodeProof, Graph, Waiting}
import frflow.protocol.*
import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}

/** A node with everything around it: what `show` and the review read. `beside`: under each parent, the other
  * parts that with it make the parent; `keptBy`: for an invariant, the contracts that keep it (or are exempt);
  * `defs`: the Scala functions its formal statement calls, and those they call.
  */
final case class NodeDetails(node: Reviewed, isRoot: Boolean, trusted: Boolean, idea: String, parents: List[Reviewed],
    beside: List[(NodeId, List[Reviewed])], above: List[Reviewed], parts: List[Reviewed], designs: List[Reviewed],
    definitions: List[Reviewed], usedBy: List[Reviewed], calls: List[Reviewed], calledBy: List[Reviewed], keptBy: List[Reviewed],
    rivals: List[Reviewed], terms: List[Term], defs: List[DefText], codeProof: Option[CodeProof], diff: NodeDiff)
    derives Codec.AsObject

/** A term of a node's vocabulary: what it means in the world, and the definition that fixes it. */
final case class Term(name: String, means: String, operation: Boolean, definedBy: Option[NodeId]) derives Codec.AsObject
/** What changed since a node was decided, by cause; `statementStale`: what it says formally changed, and its words did not. */
final case class NodeDiff(id: NodeId, causes: List[Cause], since: Option[Decision], self: List[FieldChange],
    partsAdded: List[NodeId], partsRemoved: List[NodeId], moved: List[MovedAbove], rejectedParents: List[NodeId],
    revisit: Option[Decision], code: Option[CodeChange], statementStale: Boolean) derives Codec.AsObject:
  def isEmpty: Boolean = self.isEmpty && partsAdded.isEmpty && partsRemoved.isEmpty && moved.isEmpty &&
    rejectedParents.isEmpty && revisit.isEmpty && code.isEmpty

/** An ancestor (or a definition used, a contract called) whose meaning moved since the node was decided. */
final case class MovedAbove(id: NodeId, acceptedAgain: Boolean, reason: Option[String], changes: List[FieldChange])
    derives Codec.AsObject
final case class FieldChange(field: String, lines: List[DiffLine]) derives Codec.AsObject

/** In JSON `{"op": "same", "text": ...}`, `{"op": "folded", "lines": n}`: its kind a lowercase string, as other enums are. */
enum DiffLine:
  case Same(text: String)
  case Added(text: String)
  case Removed(text: String)
  case Folded(lines: Int)

object DiffLine:
  given Codec[DiffLine] = Codec.from(
    Decoder[String].at("op").flatMap {
      case "same" => Decoder[String].at("text").map(Same(_))
      case "added" => Decoder[String].at("text").map(Added(_))
      case "removed" => Decoder[String].at("text").map(Removed(_))
      case "folded" => Decoder[Int].at("lines").map(Folded(_))
      case other => Decoder.failedWithMessage(s"no diff line op $other")
    },
    Encoder.AsObject.instance {
      case Same(t) => JsonObject("op" -> Json.fromString("same"), "text" -> Json.fromString(t))
      case Added(t) => JsonObject("op" -> Json.fromString("added"), "text" -> Json.fromString(t))
      case Removed(t) => JsonObject("op" -> Json.fromString("removed"), "text" -> Json.fromString(t))
      case Folded(n) => JsonObject("op" -> Json.fromString("folded"), "lines" -> Json.fromInt(n))
    })

/** How the code a node governs changed since it was decided (a git diff), or, never decided, the files in full. */
final case class CodeChange(files: List[String], text: String, inFull: Boolean) derives Codec.AsObject

/** A decided node gone from the model, with its last decision; `renamedTo`: a node in the model that says the same. */
final case class GoneNode(gone: Gone, renamedTo: Option[NodeId]) derives Codec.AsObject

object Details:
  /** The node, if it is gone from the model. */
  def gone(v: View, id: NodeId): Option[GoneNode] = v.annotated.gone.find(_.id == id).map(gone(v, _))
  def gone(v: View, g: Gone): GoneNode =
    def said(s: String) = s.replaceAll("\\s+", " ").trim
    val statement = said(g.decision.content.statement)
    GoneNode(g, v.nodes.find(r => statement.nonEmpty && said(r.node.content.statement) == statement).map(_.id))

  def of(v: View, r: Reviewed, code: Option[CodeChange]): NodeDetails =
    val (designs, parts) = r.node.parts.flatMap(v.node).partition(_.node.kind == NodeKind.Design)
    val parents = r.node.parents.flatMap(v.node)
    // Nearest first (see `Graph.ancestry`): their reasons say when to revisit them.
    val above = Graph(v.snapshot).ancestry(r.node).filter(_ != r.id).flatMap(v.node)
    NodeDetails(r, v.isRoot(r), v.snapshot.trusted.contains(r.id), idea(v, r, above), parents,
      parents.map(p => p.id -> p.node.parts.filter(_ != r.id).flatMap(v.node)), above, parts, designs,
      r.node.uses.flatMap(v.node), v.nodes.filter(_.node.uses.contains(r.id)), r.node.relies.flatMap(v.node),
      v.nodes.filter(_.node.relies.contains(r.id)), v.nodes.filter(_.node.invariants.exists(_.id == r.id)),
      r.review.rivals.flatMap(v.node), terms(v, r), defs(v, r), CodeProof.of(r.node), diff(v, r, code))

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

/** A node's content as fields people read, and what changed between two contents, field by field. */
object Fields:
  private val labels = Map("uses" -> "definitions used", "notModelled" -> "not modelled", "ideaSection" -> "idea section",
    "definition" -> "definition (as written)", "op" -> "operation", "keeps" -> "invariants kept")
  /** What Lean reads of a node (its `sources`). */
  val formal: Set[String] = Set("formula", "post", "rule", "check")

  /** The source as written comes last: it repeats the rest. */
  def of(c: Content): List[(String, String)] =
    val flat = c.fields.flatMap((k, j) =>
      j.asObject.filter(_ => k == "sources").fold(List(labels.getOrElse(k, k) -> text(j)))(_.toList.map((s, v) => s -> text(v))))
    val (source, rest) = flat.partition(_._1 == labels("definition"))
    rest ++ source

  private def text(j: Json): String =
    j.asString.orElse(j.asArray.map(_.map(x => x.asString.getOrElse(Canonical.print(x))).mkString("\n"))).getOrElse(Canonical.print(j))

  /** The source as written only when nothing else changed. */
  def changes(before: Content, after: Content): List[FieldChange] =
    val (a, b) = (of(before).toMap, of(after))
    val changed = (b.map(_._1) ++ of(before).map(_._1)).distinct.flatMap { k =>
      val (was, now) = (a.getOrElse(k, ""), b.toMap.getOrElse(k, ""))
      Option.when(was != now)(FieldChange(k, LineDiff(was, now)))
    }
    val (source, rest) = changed.partition(_.field == labels("definition"))
    if rest.isEmpty then source else rest

/** A line diff by longest common subsequence; an unchanged run more than `context` lines from a change is folded. */
object LineDiff:
  /** Beyond this many line pairs the whole text is shown as replaced. */
  private val Budget = 250000

  def apply(before: String, after: String, context: Int = 1): List[DiffLine] =
    def lines(s: String) = if s.isEmpty then Vector.empty else s.split("\n", -1).toVector
    val (a, b) = (lines(before), lines(after))
    fold(if a.size.toLong * b.size > Budget then (a.map(DiffLine.Removed(_)) ++ b.map(DiffLine.Added(_))).toList else align(a, b), context)

  private def align(a: Vector[String], b: Vector[String]): List[DiffLine] =
    // common(i)(j): the length of the longest common subsequence of a.drop(i) and b.drop(j).
    val common = Array.ofDim[Int](a.size + 1, b.size + 1)
    for i <- a.indices.reverse; j <- b.indices.reverse do
      common(i)(j) = if a(i) == b(j) then common(i + 1)(j + 1) + 1 else common(i + 1)(j).max(common(i)(j + 1))
    def walk(i: Int, j: Int, acc: List[DiffLine]): List[DiffLine] =
      if i < a.size && j < b.size && a(i) == b(j) then walk(i + 1, j + 1, DiffLine.Same(a(i)) :: acc)
      else if i < a.size && (j == b.size || common(i + 1)(j) >= common(i)(j + 1)) then walk(i + 1, j, DiffLine.Removed(a(i)) :: acc)
      else if j < b.size then walk(i, j + 1, DiffLine.Added(b(j)) :: acc)
      else acc.reverse
    walk(0, 0, Nil)

  private def fold(ops: List[DiffLine], context: Int): List[DiffLine] =
    def same(l: DiffLine) = PartialFunction.cond(l) { case DiffLine.Same(_) => true }
    // The lines within `context` of a change: the change itself among them.
    val near = ops.zipWithIndex.collect { case (l, k) if !same(l) => (k - context) to (k + context) }.flatten.toSet
    ops.zipWithIndex.map((l, k) => Option.when(near(k))(l))
      .foldRight(List.empty[DiffLine]) {
        case (Some(l), acc) => l :: acc
        case (None, DiffLine.Folded(n) :: rest) => DiffLine.Folded(n + 1) :: rest
        case (None, acc) => DiffLine.Folded(1) :: acc
      }
