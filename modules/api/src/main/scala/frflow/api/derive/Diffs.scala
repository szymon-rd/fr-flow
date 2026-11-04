package frflow.api.derive

import frflow.api.view.diff.*
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.content.{Content, FieldValue}
import frflow.decision.review.{Meaning, Moves, Subject}
import frflow.project.pipeline.Analysis

/** What moved under a node's decision, from the analysis; its code's diff is read by the shell (`files` and
  * `commit` say what to ask git).
  */
private[api] object Diffs:
  /** None when the model has no such node. */
  def of(a: Analysis, id: NodeId, code: Option[String]): Option[NodeDiff] = a.subjects.get(id).map { s =>
    val decided = a.inputs.ledger.counting.binding(id).map(_.bound.content)
    NodeDiff(decided.fold(Nil)(fields(_, s.content)), above(a, s), decided.fold(Parts(Nil, Nil))(parts(_, s.content)),
      code)
  }

  /** The governed files and the commit its decision was taken at, when it has both: what its code's diff is of. */
  def code(a: Analysis, id: NodeId): Option[(String, List[RelPath])] =
    for
      commit <- a.inputs.ledger.counting.binding(id).flatMap(_.author.commit)
      files  <- a.governed.get(id).map(_.files.flatMap(RelPath.parse(_).toOption)).filter(_.nonEmpty)
    yield commit -> files

  /** Each field of its own content (its place left out: parts are listed apart) that moved, as a line diff. */
  def fields(was: Content, now: Content): List[FieldDiff] =
    val (before, after) = (Meaning.own(was), Meaning.own(now))
    (before.fields.map(_._1) ++ after.fields.map(_._1)).distinct.flatMap { f =>
      val (b, n) = (before.get(f).toList.flatMap(lines), after.get(f).toList.flatMap(lines))
      Option.when(b != n)(FieldDiff(f, Lines.diff(b, n)))
    }

  private def above(a: Analysis, s: Subject): List[Moved] =
    Moves.movedAbove(a.reading, s).map((m, was) =>
      Moved(m, fields(was, a.subjects.get(m).fold(Content.empty)(_.content))))

  private def parts(was: Content, now: Content): Parts =
    val (before, after) = (was.texts("parts"), now.texts("parts"))
    Parts(after.filterNot(before.contains).map(NodeId(_)), before.filterNot(after.contains).map(NodeId(_)))

  private def lines(v: FieldValue): List[String] = v match
    case FieldValue.Text(t)    => t.split("\n", -1).toList
    case FieldValue.Texts(ts)  => ts
    case FieldValue.Record(fs) => fs.map((k, x) => s"$k: $x")
