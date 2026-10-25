package sharing.domain

import frflow.*

/** Everything the service keeps: the documents, the folders, the teams, and the shares. */
final case class Library(documents: List[Document], folders: List[Folder], teams: List[Team], shares: List[Share])
object Library extends Data[Library]
