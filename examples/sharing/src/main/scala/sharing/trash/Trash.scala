package sharing.trash

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.time.Lifetimes.gone
import sharing.time.Run.{after, events, housekeepingWithin}

/** The trash: someone who may edit a document puts it in the trash, where it gives nobody access; they may restore it
  * until it is gone, and housekeeping purges it once it is. Each method is a function of the library and of the moment.
  */
trait Trash:
  /** The library after `by` puts `doc` in the trash. */
  def trash(library: Library, now: BigInt, by: PersonId, doc: DocumentId): Library
  /** The library after `by` restores `doc` from the trash. */
  def restore(library: Library, now: BigInt, by: PersonId, doc: DocumentId): Library

/** The trash's contracts, each with its code. */
object Trash:
  import Demo.*

  val trash = Param[(Library, BigInt, PersonId, DocumentId) => Library]("the library after someone asks to put a document in the trash")
  val restore = Param[(Library, BigInt, PersonId, DocumentId) => Library]("the library after someone asks to restore a document from the trash")

  /** The branch: what the trash is. Its parts are the two operations and, below the timed word "gone", the deadline by
    * which housekeeping purges a document gone.
    */
  val trashUntilGone = Node.claim("Only someone who may edit a document puts it in the trash or takes it out, and only before it is gone; and housekeeping purges it within one of its periods of its being gone.",
    why = "Q8: the trash is a delay before deleting: what is in it can be brought back until it is gone, and not after. Whether it is gone is left open here (Lifetimes); that a gone document does not linger is what TrashPurgedOnTime says with the clock.",
    idea = "Trash"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    (trash(lib, t, by, d) =!= lib implies mayEdit(lib, t, by, Target[Target.Doc](d))) &&
    (restore(lib, t, by, d) =!= lib implies (mayEdit(lib, t, by, Target[Target.Doc](d)) &&
      lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t))))) &&
    after(events).library.documents.forall(doc => !gone(doc, after(events).now - housekeepingWithin)))
    .refines(accessFollowsShares)

  private val planInTrash = library.copy(documents = List(planTrashed, q3ReportDoc))

  val trashContract = Node.contract("Someone who may edit a document puts it in the trash: it is in the trash from now on, unless it was already, when it keeps the time it was put there. When anyone else asks, nothing changes.",
    why = "Q8: deleting a document puts it in the trash for a while rather than deleting it for good. Deleting is a change to the document, so only someone who may edit it does it.",
    idea = "Trash"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    trash(lib, t, by, d) === mayEdit(lib, t, by, Target[Target.Doc](d)).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d && !doc.trashed.isDefined).fold(doc.copy((trashed = some(t))), doc)))), lib)))
    .refines(trashUntilGone)
    .examples()(
      allows(library, now - day, ann, plan, planInTrash, "Ann may edit the plan: it goes to the trash"),
      allows(planInTrash, now, ann, plan, planInTrash, "already in the trash: it keeps its time"),
      allows(library, now, bob, plan, library, "Bob may not edit the plan"),
      forbids(library, now, bob, q3Report, library.copy(documents = List(planDoc, q3ReportDoc.copy(trashed = Some(now)))),
        "Bob may only view the Q3 report: he cannot delete it"))

  val trashCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    mayEdit(lib, t, by, Target[Target.Doc](d)).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d && !doc.trashed.isDefined).fold(doc.copy((trashed = some(t))), doc)))), lib)
  }

  /** Whether `by` may restore the document now: they may edit it, and it is in the trash and not yet gone. */
  val mayRestore = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    mayEdit(lib, t, by, Target[Target.Doc](d)) && lib.documents.exists(doc => doc.id === d && doc.trashed.isDefined && !gone(doc, t))
  }

  val restoreContract = Node.contract("Someone who may edit a document restores it from the trash before it is gone: it is out of the trash, and its shares give access again. When anyone else asks, or it is not in the trash, or it is gone, nothing changes.",
    why = "Q8: a document in the trash can be restored until it is gone; its shares stayed, so restoring brings back exactly the access it had.",
    idea = "Trash"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    restore(lib, t, by, d) === mayRestore(lib, t, by, d).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d && !gone(doc, t)).fold(doc.copy((trashed = none[BigInt])), doc)))), lib)))
    .refines(trashUntilGone)
    .examples()(
      allows(planInTrash, now, ann, plan, library, "a day in the trash: Ann restores the plan"),
      allows(planInTrash, now + 29 * day, ann, plan, planInTrash, "thirty days in the trash: it is gone"),
      allows(planInTrash, now, bob, plan, planInTrash, "Bob may not edit the plan"),
      forbids(planInTrash, now + 40 * day, ann, plan, library, "a document gone is never restored"))

  val restoreCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId]) =>
    mayRestore(lib, t, by, d).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d && !gone(doc, t)).fold(doc.copy((trashed = none[BigInt])), doc)))), lib)
  }
