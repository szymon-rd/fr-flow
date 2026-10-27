package sharing.ownership

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout

/** Ownership: every document has one owner, who alone hands it on. The owner's own shares of their document are
  * theirs: nobody unshares or replaces them. A function of the library and of the moment.
  */
object Ownership:
  val transfer = Definition[(Library, BigInt, PersonId, DocumentId, PersonId) => Library](
    "the library after someone asks to hand a document on")

  /** Whether `by` owns the document. */
  val owns = define { (lib: Term[Library], by: Term[PersonId], d: Term[DocumentId]) =>
    lib.documents.exists(doc => doc.id === d && doc.owner === by) }

  /** The owner's edit share of a document for good. */
  val ownersEdit = define { (d: Term[DocumentId], to: Term[PersonId]) =>
    make[Share](make[Target.Doc](d), make[Grantee.Person](to), Level.Edit: Term[Level], none[BigInt]) }

  /** The documents with one handed on to a new owner. */
  val handedOn = define { (lib: Term[Library], d: Term[DocumentId], to: Term[PersonId]) =>
    lib.documents.map(doc => when(doc.id === d)(doc.updated(_.owner, to)).otherwise(doc)) }

  val transferCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      when(owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) && mayEdit(lib, t, to, make[Target.Doc](d)))(
        lib.updated(_.documents, handedOn(lib, d, to))
          .updated(_.shares, ownersEdit(d, to) ::
            sharesWithout(lib.shares, make[Target.Doc](d), make[Grantee.Person](to)))).otherwise(lib) }
