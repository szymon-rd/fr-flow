package sharing.trash

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.gone

/** The trash: someone who may edit a document puts it in the trash, where it gives nobody access; they may restore it
  * until it is gone, and housekeeping purges it once it is. Each operation is a function of the library and of the
  * moment.
  */
object Trash:
  val trash = Definition[(Library, BigInt, PersonId, DocumentId) => Library](
    "the library after someone asks to put a document in the trash")
  val restore = Definition[(Library, BigInt, PersonId, DocumentId) => Library](
    "the library after someone asks to restore a document from the trash")

  val trashCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    when(mayEdit(lib, t, by, make[Target.Doc](d)))(lib.updated(_.documents, lib.documents.map(doc =>
      when(doc.id === d && !doc.trashed.isDefined)(doc.updated(_.trashed, some(t))).otherwise(doc)))).otherwise(lib) }

  /** Whether `by` may restore the document now: they may edit it, and it is in the trash and not yet gone. */
  val mayRestore = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    mayEdit(lib, t, by, make[Target.Doc](d)) &&
      lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t)) }

  val restoreCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    when(mayRestore(lib, t, by, d))(lib.updated(_.documents, lib.documents.map(doc =>
      when(doc.id === d && !gone(doc, t))(doc.updated(_.trashed, none[BigInt])).otherwise(doc)))).otherwise(lib) }
