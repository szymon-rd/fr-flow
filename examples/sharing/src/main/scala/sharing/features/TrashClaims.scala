package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Trash.{mayRestore, restore, trash}
import sharing.time.Lifetimes.gone

/** Trash's claims: what its code is proven to do, each refining a branch or the purpose. */
object TrashClaims:
  val trashContract = Node.claim("Trashing, asked by someone who may edit the document, puts it in the trash now " +
      "unless it is there already, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => trash(lib, t, by, d) ===
      when(mayEdit(lib, t, by, make[Target.Doc](d)))(lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d && !doc.trashed.isDefined)(doc.updated(_.trashed, some(t))).otherwise(doc)))).otherwise(lib)))
    .refines(onlyEditorsTrash)

  val restoreContract = Node.claim("Restoring, asked by someone who may edit the document while it is in the trash " +
      "and not gone, takes it out of the trash, and otherwise changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) => restore(lib, t, by, d) ===
      when(mayRestore(lib, t, by, d))(lib.updated(_.documents, lib.documents.map(doc =>
        when(doc.id === d && !gone(doc, t))(doc.updated(_.trashed, none[BigInt])).otherwise(doc)))).otherwise(lib)))
    .refines(onlyEditorsTrash, restoredOnlyBeforeGone)
