package frflow.api.shell

import cats.effect.Async
import cats.syntax.all.*
import frflow.api.Reading
import frflow.api.derive.{Diffs, Finds}
import frflow.api.view.diff.NodeDiff
import frflow.api.view.{Found, View}
import frflow.core.name.NodeId
import frflow.decision.content.Sha

/** `Reading` over a session: each read analyses the project once. */
private[api] final class Reads[F[_]: Async](s: Session[F]) extends Reading[F]:
  def view: F[View] = s.analysis.flatMap(s.view)

  /** Its code's diff is git's, since the commit its decision was taken at; none when there is nothing to show. */
  def diff(id: NodeId): F[Option[NodeDiff]] = s.analysis.flatMap { a =>
    Diffs.code(a, id).flatTraverse((commit, files) => s.guarded(s.ports.git.diff(commit, files))
      .map(d => Option.when(d.nonEmpty)(d))).map(Diffs.of(a, id, _))
  }

  def find(query: String): F[Found] = s.analysis.map(Finds.of(_, query))

  /** The sources' paths and texts, sorted, hashed together. */
  def modelFingerprint: F[String] = s.guarded(
    s.project.sources.flatTraverse(s.ports.files.list).map(_.distinct.sorted)
      .flatMap(_.traverse(p => s.ports.files.read(p).map(t => List(p.value, t.getOrElse("")))))
      .map(texts => Sha.parts(texts.flatten*)))
