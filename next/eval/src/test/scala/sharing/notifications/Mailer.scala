package sharing.notifications

import frflow.*
import sharing.domain.*

/** The mail server, as proven code sees it: it takes a notice to deliver; its model is each person's mailbox, the
  * notices delivered to them, each once, oldest first, by person (today's `PersonId → List Notice`). Order is kept
  * per person, not across people: two people's deliveries change two mailboxes, in either order.
  */
object Mailer:
  val send = Definition[Notice => Flow[Unit]]("a notice given to the mail server to deliver")

  /** A person's mailbox: the notices delivered to them, oldest first. */
  val mailbox = define { (boxes: Term[Map[PersonId, List[Notice]]], p: Term[PersonId]) =>
    boxes.getOrElse(p, Nil: Term[List[Notice]]) }
  /** A mailbox after a notice is given to the mail server: the notice at the end, unless it is there already. */
  val taken = define { (ns: Term[List[Notice]], n: Term[Notice]) => when(ns.contains(n))(ns).otherwise(ns :+ n) }
  /** The mailboxes with a person's replaced. */
  val withMailbox = define { (boxes: Term[Map[PersonId, List[Notice]]], p: Term[PersonId], ns: Term[List[Notice]]) =>
    boxes.updated(p, ns) }

  object mailerModel extends StateModel.failing[Map[PersonId, List[Notice]], Failure](
      "the mail server the service sends notices to; it may be down", Failure.MailerUnavailable):
    send.means(notice => state.update(boxes => withMailbox(boxes, notice.to, taken(mailbox(boxes, notice.to), notice))))
