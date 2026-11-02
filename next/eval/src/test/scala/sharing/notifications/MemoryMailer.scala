package sharing.notifications

import cats.effect.{IO, Ref}
import cats.syntax.all.*
import sharing.domain.{Mailbox, Notice}

/** The mail server kept in memory: each person's mailbox, a notice delivered once, at the end; the mailer's Scala for
  * development and tests, tested against `mailerModel`. Each call takes the next of the faults it is given (`true`:
  * that call fails and delivers nothing), and succeeds when none is left.
  */
final class MemoryMailer private (held: Ref[IO, List[Mailbox]], faults: Ref[IO, List[Boolean]]):
  def send(n: Notice): IO[Unit] = up *> held.update { boxes =>
    val mine = boxes.find(_.person == n.to).fold(List.empty[Notice])(_.notices)
    Mailbox(n.to, if mine.contains(n) then mine else mine :+ n) :: boxes.filterNot(_.person == n.to)
  }
  def boxes: IO[List[Mailbox]] = held.get
  /** The faults the next calls take, in order. */
  def failing(fs: List[Boolean]): IO[Unit] = faults.set(fs)

  private def up: IO[Unit] = faults.modify {
    case f :: rest => (rest, f)
    case Nil       => (Nil, false)
  }.flatMap(f => IO.raiseError(IllegalStateException("the mailer is down")).whenA(f))

object MemoryMailer:
  def holding(boxes: List[Mailbox]): IO[MemoryMailer] =
    (Ref[IO].of(boxes), Ref[IO].of(List.empty[Boolean])).mapN(MemoryMailer(_, _))
