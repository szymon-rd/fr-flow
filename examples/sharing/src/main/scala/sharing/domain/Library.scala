package sharing.domain

import frflow.*

/** Everything the service keeps: the documents, the folders, the teams, the shares, and the invitations pending. */
final case class Library(documents: List[Document], folders: List[Folder], teams: List[Team], shares: List[Share],
    invitations: List[Invitation])
object Library extends Data[Library]
