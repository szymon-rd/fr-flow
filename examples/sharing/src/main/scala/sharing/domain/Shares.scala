package sharing.domain

import frflow.*

/** How much a share lets someone do: view, or edit (which includes viewing). */
enum Level:
  case View, Edit
object Level extends Data[Level]

/** What is shared: one document, or a folder with everything inside it. */
enum Target:
  case Doc(id: DocumentId)
  case InFolder(id: FolderId)
object Target extends Data[Target]

/** Who something is shared with: one person, or a team (everyone in it). */
enum Grantee:
  case Person(id: PersonId)
  case Team(id: TeamId)
object Grantee extends Data[Grantee]

/** A share: what is shared, with whom, at which level, and until when (in seconds; `None`: no end). A share is in force
  * until its end (Lifetimes.InForceContract); after it, it gives no access, whether or not housekeeping has removed it.
  */
final case class Share(what: Target, withWhom: Grantee, level: Level, until: Option[BigInt])
object Share extends Data[Share]:
  given LeanType[Share] = LeanType.product[Share]
