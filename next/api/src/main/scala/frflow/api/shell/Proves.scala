package frflow.api.shell

import cats.Parallel
import cats.effect.Async
import cats.effect.std.Queue
import cats.syntax.all.*
import fs2.Stream
import frflow.api.Proving
import frflow.api.derive.Stubs
import frflow.api.view.{CheckEvent, Stop, View}
import frflow.core.name.{NodeId, RelPath}
import frflow.project.check.{CheckProgram, Render}
import frflow.project.pipeline.Analysis
import frflow.project.program.{StatusProgram, TestProgram}

/** `Proving` over a session: a check is Lean's (`CheckProgram`, level by level) then the tests before production
  * (`TestProgram`), both recorded; its levels stream as they start.
  */
private[api] final class Proves[F[_]: Async: Parallel](s: Session[F]) extends Proving[F]:
  private val files = s.ports.files
  private val library = s.library.path

  def render: F[List[String]] =
    s.analysis.flatMap(a => s.guarded(Render(files, library)(a))).map(_.map(_.dotted))

  def status: F[View] = s.analysis.flatMap(a => s.guarded(StatusProgram(files, library)(a)) >> s.view(a))

  def check(only: Option[NodeId]): Stream[F, CheckEvent] = checked(only, _ => Async[F].unit)

  def ci: Stream[F, CheckEvent] = checked(None, a => StatusProgram(files, library)(a).void)

  def scaffold(id: NodeId): F[Option[RelPath]] = s.analysis.flatMap { a =>
    if a.decided.theory.node(id).isEmpty then Async[F].raiseError(Stop.UnknownNode(id))
    else Stubs.of(a, id).traverse((p, text) => s.guarded(files.writeIfChanged(p, text)).as(p))
  }

  /** The check's events, `after` run on the analysis it ends with before the view is read. */
  private def checked(only: Option[NodeId], after: Analysis => F[Unit]): Stream[F, CheckEvent] =
    Stream.eval(Queue.unbounded[F, Option[CheckEvent]]).flatMap { q =>
      val run = for
        a                <- s.analysis
        lake             <- s.lean(a)
        (proven, byLean) <- s.guarded(CheckProgram(files, lake, library, s.code)
                              .run(a, only, (i, n, ids) => q.offer(Some(CheckEvent.Level(i, n, ids)))))
        (tested, byTests) <- s.guarded(TestProgram(files, s.code, s.models)(byLean, only))
        _                <- s.guarded(after(byTests))
        view             <- s.view(byTests)
        checked           = (proven.map(_.node) ++ tested.map(_._1)).distinct
        _                <- q.offer(Some(CheckEvent.Done(checked, view))) >> q.offer(None)
      yield ()
      Stream.fromQueueNoneTerminated(q).concurrently(Stream.eval(run))
    }
