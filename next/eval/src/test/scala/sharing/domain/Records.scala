package sharing.domain

import frflow.*

/** A person's request for access to a document, at a level, made at a time (in seconds). It gives no access: someone
  * who may edit the document approves it (which makes the share) or declines it. `reminded`: whether the owner has been
  * reminded of it, which housekeeping does once, after 48 hours; after 7 days it lapses (it is declined).
  */
final case class AccessRequest(person: PersonId, what: Target, level: Level, asked: BigInt, reminded: Boolean)
    derives LeanType

/** A change the log keeps: a request that changed the library, or a run of housekeeping that did; or, for an entry more
  * than a year old, nothing any more: its change is forgotten (the log is kept for a year).
  */
enum Change derives LeanType:
  case Made(request: Request)
  case Housekept
  case Forgotten

/** An entry of the log: its number (its place in the log, from 0), when it was made (in seconds), and the change. */
final case class Entry(id: BigInt, at: BigInt, change: Change) derives LeanType

/** What a notice is about (its event): a change logged, a reminder of an access request, that one lapsed, or a share
  * ending. The event is the notice's id: the mail server delivers a notice of it to a person once.
  */
enum Subject derives LeanType:
  case Logged(entry: Entry)
  case Reminder(request: AccessRequest)
  case Lapsed(request: AccessRequest)
  case Ending(share: Share)

/** A notice to send: a person to tell of an event. */
final case class Notice(to: PersonId, about: Subject) derives LeanType

/** Why a request or a run of a job fails: the store, or the mail server, is not answering. */
enum Failure derives LeanType:
  case StoreUnavailable, MailerUnavailable

/** A person's mailbox at the mail server: the notices delivered to them, oldest first. */
final case class Mailbox(person: PersonId, notices: List[Notice]) derives LeanType
