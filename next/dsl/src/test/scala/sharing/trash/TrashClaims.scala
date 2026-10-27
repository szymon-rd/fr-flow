package sharing.trash

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.gone
import sharing.trash.Trash.{mayRestore, restore, trash}

/** Trash's claims: what its code is proven to do, each refining a branch or the purpose. */
object TrashClaims:
  val trashContract = Node.claim("Someone who may edit a document puts it in the trash: it is in the trash from now " +
      "on, unless it was already, when it keeps the time it was put there. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => trash(lib, t, by, d) ===
      when(mayEdit(lib, t, by, make[Target.Doc](d)))(lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d && !doc.trashed.isDefined)(doc.updated(_.trashed, some(t))).otherwise(doc)))).otherwise(lib)))
    .refines(trashUntilGone)

  val restoreContract = Node.claim("Someone who may edit a document restores it from the trash before it is gone: " +
      "it is out of the trash, and its shares give access again. When anyone else asks, or it is not in the trash, " +
      "or it is gone, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => restore(lib, t, by, d) ===
      when(mayRestore(lib, t, by, d))(lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d && !gone(doc, t))(doc.updated(_.trashed, none[BigInt])).otherwise(doc)))).otherwise(lib)))
    .refines(trashUntilGone)
