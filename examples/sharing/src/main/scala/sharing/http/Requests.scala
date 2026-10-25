package sharing.http

import frflow.*
import sharing.domain.*

/** What a client asks the service: a person's access to a document, or a change someone asks to make. */
enum Request:
  case Access(person: PersonId, doc: DocumentId)
  case Share(by: PersonId, what: Target, withWhom: Grantee, level: Level)
  case Unshare(by: PersonId, what: Target, withWhom: Grantee)
  case Move(by: PersonId, doc: DocumentId, into: Option[FolderId])
object Request extends Data[Request]

/** What the service answers: the person's access; or that the change was made; or that the asker may not make it. */
enum Answer:
  case Access(level: Option[Level])
  case Done
  case Refused
object Answer extends Data[Answer]
