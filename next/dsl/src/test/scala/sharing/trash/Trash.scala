package sharing.trash

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.gone
import sharing.time.Run.{after, events, housekeepingWithin}

/** The trash: someone who may edit a document puts it in the trash, where it gives nobody access; they may restore it
  * until it is gone, and housekeeping purges it once it is. Each operation is a function of the library and of the
  * moment.
  */
object Trash:
  val trash = Definition[(Library, BigInt, PersonId, DocumentId) => Library](
    "the library after someone asks to put a document in the trash")
  val restore = Definition[(Library, BigInt, PersonId, DocumentId) => Library](
    "the library after someone asks to restore a document from the trash")

  /** The branch: what the trash is. */
  val trashUntilGone = Node.claim("Only someone who may edit a document puts it in the trash or takes it out, and " +
      "only before it is gone; and housekeeping purges it within one of its periods of its being gone.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
      (trash(lib, t, by, d) =!= lib implies mayEdit(lib, t, by, make[Target.Doc](d))) &&
        (restore(lib, t, by, d) =!= lib implies (mayEdit(lib, t, by, make[Target.Doc](d)) &&
          lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t))))) &&
    after(events).library.documents.forall(doc => !gone(doc, after(events).now - housekeepingWithin)))
    .refines(accessFollowsShares)

  val trashContract = Node.claim("Someone who may edit a document puts it in the trash: it is in the trash from now " +
      "on, unless it was already, when it keeps the time it was put there. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => trash(lib, t, by, d) ===
      when(mayEdit(lib, t, by, make[Target.Doc](d)))(lib.updated(_.documents, lib.documents.mapped(doc =>
        when(doc.id === d && !doc.trashed.isDefined)(doc.updated(_.trashed, some(t))).otherwise(doc)))).otherwise(lib)))
    .refines(trashUntilGone)

  val trashCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    when(mayEdit(lib, t, by, make[Target.Doc](d)))(lib.updated(_.documents, lib.documents.mapped(doc =>
      when(doc.id === d && !doc.trashed.isDefined)(doc.updated(_.trashed, some(t))).otherwise(doc)))).otherwise(lib) }

  /** Whether `by` may restore the document now: they may edit it, and it is in the trash and not yet gone. */
  val mayRestore = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    mayEdit(lib, t, by, make[Target.Doc](d)) &&
      lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t)) }

  val restoreContract = Node.claim("Someone who may edit a document restores it from the trash before it is gone: " +
      "it is out of the trash, and its shares give access again. When anyone else asks, or it is not in the trash, " +
      "or it is gone, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => restore(lib, t, by, d) ===
      when(mayRestore(lib, t, by, d))(lib.updated(_.documents, lib.documents.mapped(doc =>
        when(doc.id === d && !gone(doc, t))(doc.updated(_.trashed, none[BigInt])).otherwise(doc)))).otherwise(lib)))
    .refines(trashUntilGone)

  val restoreCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    when(mayRestore(lib, t, by, d))(lib.updated(_.documents, lib.documents.mapped(doc =>
      when(doc.id === d && !gone(doc, t))(doc.updated(_.trashed, none[BigInt])).otherwise(doc)))).otherwise(lib) }
