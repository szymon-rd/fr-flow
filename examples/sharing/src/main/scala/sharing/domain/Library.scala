package sharing.domain

import frflow.*

/** Everything the service keeps: the documents, the folders, the teams, the shares, the invitations and the access
  * requests pending; the log of the changes made, oldest first; and the notices still to send (the outbox). The log
  * and the outbox are kept with what they record, so a change, its entry and its notice are saved together.
  */
final case class Library(documents: List[Document], folders: List[Folder], teams: List[Team], shares: List[Share],
    invitations: List[Invitation], requests: List[AccessRequest], log: List[Entry], outbox: List[Notice])
object Library extends Data[Library]:
  given LeanType[Library] = LeanType.product[Library]
