package sharing.domain

import frflow.*

/** What a client asks the service: a person's access to a document, or a change someone asks to make. */
enum Request:
  case Access(person: PersonId, doc: DocumentId)
  case Share(by: PersonId, what: Target, withWhom: Grantee, level: Level, until: Option[BigInt])
  case Unshare(by: PersonId, what: Target, withWhom: Grantee)
  case Move(by: PersonId, doc: DocumentId, into: Option[FolderId])
  case Invite(by: PersonId, to: PersonId, what: Target, level: Level)
  case Accept(person: PersonId, what: Target)
  case Withdraw(by: PersonId, to: PersonId, what: Target)
  case Trash(by: PersonId, doc: DocumentId)
  case Restore(by: PersonId, doc: DocumentId)
  /** A person asks for access to a document, at a level. */
  case Ask(person: PersonId, doc: DocumentId, level: Level)
  /** Someone who may edit a document approves a person's request for it. */
  case Approve(by: PersonId, person: PersonId, doc: DocumentId)
  /** Someone who may edit a document declines a person's request for it. */
  case Decline(by: PersonId, person: PersonId, doc: DocumentId)
  /** A document's owner hands it on to another person. */
  case Transfer(by: PersonId, doc: DocumentId, to: PersonId)
object Request extends Data[Request]:
  // Derived once, here: derived where it is used, it is inlined at each use.
  given LeanType[Request] = LeanType.sum[Request]

/** What the service answers: the person's access; or that the change was made; or that the asker may not make it. */
enum Answer:
  case Access(level: Option[Level])
  case Done
  case Refused
object Answer extends Data[Answer]:
  given LeanType[Answer] = LeanType.sum[Answer]
