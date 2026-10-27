package sharing.domain

import frflow.*

/** How much a share lets someone do: view, or edit (which includes viewing). */
enum Level derives LeanType:
  case View, Edit

/** What is shared: one document, or a folder with everything inside it. */
enum Target derives LeanType:
  case Doc(id: DocumentId)
  case InFolder(id: FolderId)

/** Who something is shared with: one person, or a team (everyone in it). */
enum Grantee derives LeanType:
  case Person(id: PersonId)
  case Team(id: TeamId)

/** A share: what is shared, with whom, at which level, and until when (in seconds; `None`: no end). A share is in force
  * until its end; after it, it gives no access, whether or not housekeeping has removed it.
  */
final case class Share(what: Target, withWhom: Grantee, level: Level, until: Option[BigInt]) derives LeanType
