package sharing.domain

import frflow.*

/** A document, named by its id. */
final case class DocumentId(name: String)
object DocumentId extends Data[DocumentId]

/** A folder, named by its id. */
final case class FolderId(name: String)
object FolderId extends Data[FolderId]

/** A document, and where it is: the folders that contain it, outermost first (empty when it is in no folder). A
  * document in `reports`, inside `finance`, is in `List(finance, reports)`: it is in its own folder and in every folder
  * around it. `trashed`: when it was moved to the trash (in seconds), `None` when it is not in the trash. `owner`: the
  * one person who owns it, who alone hands it on.
  */
final case class Document(id: DocumentId, title: String, folders: List[FolderId], trashed: Option[BigInt], owner: PersonId)
object Document extends Data[Document]:
  given LeanType[Document] = LeanType.product[Document]

/** A folder, and the folders around it, outermost first. Folders form a tree: no folder is among its own `folders`. */
final case class Folder(id: FolderId, name: String, folders: List[FolderId])
object Folder extends Data[Folder]
