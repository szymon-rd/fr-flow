package sharing.notifications

import frflow.*
import sharing.domain.*

/** The mail server, as proven code sees it: it takes a notice to deliver. */
trait Mailer[F[_], T[_]] derives BoundaryOps:
  def send(notice: T[Notice]): F[Unit]

/** The mail server as the proofs see it: each person's mailbox, the notices delivered to them, each once, oldest
  * first. Order is kept per person, not across people: two people's deliveries change two mailboxes.
  */
final class Mailboxes[F[_]: Flow](state: Model[F, List[Mailbox]]) extends Mailer[F, Term]:
  def send(notice: Term[Notice]): F[Unit] = state.get.flatMap(boxes =>
    state.set(Mailer.withMailbox(boxes, notice.to, Mailer.taken(Mailer.mailbox(boxes, notice.to), notice))))

object Mailer:
  /** A person's mailbox: the notices delivered to them, oldest first. */
  val mailbox = define { (boxes: Term[List[Mailbox]], p: Term[PersonId]) =>
    boxes.find(b => b.person === p).fold(Nil: Term[List[Notice]])(b => b.notices) }
  /** A mailbox after a notice is given to the mail server: the notice at the end, unless it is there already. */
  val taken = define { (ns: Term[List[Notice]], n: Term[Notice]) => when(ns.contains(n))(ns).otherwise(ns :+ n) }
  /** The mailboxes with a person's replaced. */
  val withMailbox = define { (boxes: Term[List[Mailbox]], p: Term[PersonId], ns: Term[List[Notice]]) =>
    make[Mailbox](p, ns) :: boxes.filter(b => b.person =!= p) }
