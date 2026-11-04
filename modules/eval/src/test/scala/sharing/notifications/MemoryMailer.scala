package sharing.notifications

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import sharing.domain.{Notice, PersonId}

/** The mail server kept in memory: each person's mailbox, a notice delivered once, at the end; the mailer's Scala for
  * development and tests, tested against `mailerModel`. Each call takes the next of the faults it is given (`true`:
  * that call fails and delivers nothing), and succeeds when none is left.
  */
final class MemoryMailer private (held: Ref[IO, Map[PersonId, List[Notice]]], faults: Ref[IO, List[Boolean]]):
  def send(n: Notice): IO[Unit] = up *> held.update { boxes =>
    val mine = boxes.getOrElse(n.to, Nil)
    boxes.updated(n.to, if mine.contains(n) then mine else mine :+ n)
  }
  def boxes: IO[Map[PersonId, List[Notice]]] = held.get
  /** The faults the next calls take, in order. */
  def failing(fs: List[Boolean]): IO[Unit] = faults.set(fs)

  private def up: IO[Unit] = faults.modify {
    case f :: rest => (rest, f)
    case Nil       => (Nil, false)
  }.flatMap(f => IO.raiseError(IllegalStateException("the mailer is down")).whenA(f))

object MemoryMailer:
  def holding(boxes: Map[PersonId, List[Notice]]): IO[MemoryMailer] =
    (Ref[IO].of(boxes), Ref[IO].of(List.empty[Boolean])).mapN(MemoryMailer(_, _))
