package sharing.domain

import frflow.*

/** A person's request for access to a document, at a level, made at a time (in seconds). It gives no access: someone
  * who may edit the document approves it (which makes the share) or declines it. `reminded`: whether the owner has been
  * reminded of it, which housekeeping does once, after 48 hours; after 7 days it lapses (it is declined).
  */
final case class AccessRequest(person: PersonId, doc: DocumentId, level: Level, asked: BigInt, reminded: Boolean)
object AccessRequest extends Data[AccessRequest]:
  given LeanType[AccessRequest] = LeanType.product[AccessRequest]

/** A change the log keeps: a request that changed the library, or a run of housekeeping that did. */
enum Change:
  case Made(request: Request)
  case Housekept
object Change extends Data[Change]:
  given LeanType[Change] = LeanType.sum[Change]

/** An entry of the log: its number (its place in the log, from 0), when it was made (in seconds), and the change. */
final case class Entry(id: Int, at: BigInt, change: Change)
object Entry extends Data[Entry]:
  given LeanType[Entry] = LeanType.product[Entry]

/** What a notice is about (its event): a change logged, a reminder of an access request, or that one lapsed. The
  * event is the notice's id: the mail server delivers a notice of it to a person once.
  */
enum Subject:
  case Logged(entry: Entry)
  case Reminder(request: AccessRequest)
  case Lapsed(request: AccessRequest)
object Subject extends Data[Subject]:
  given LeanType[Subject] = LeanType.sum[Subject]

/** A notice to send: a person to tell of an event. */
final case class Notice(to: PersonId, about: Subject)
object Notice extends Data[Notice]:
  given LeanType[Notice] = LeanType.product[Notice]

/** Why a request or a run of a job fails: the store, or the mail server, is not answering. */
enum Failure:
  case StoreUnavailable, MailerUnavailable
object Failure extends Data[Failure]
