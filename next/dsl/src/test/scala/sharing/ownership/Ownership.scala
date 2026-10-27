package sharing.ownership

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing
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

  /** The branch: what owning a document means. */
  val ownersKeepTheirDocuments = Node.claim("A document has one owner. Only its owner, while they may edit it, hands " +
      "it on, and only to someone who may edit it, who then has an edit share of it for good; and nobody unshares or " +
      "replaces an owner's shares of their own document. An owner's share is with them in person, not through a team, " +
      "so leaving a team never takes their documents from them.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      transfer(lib, t, by, d, to) =!= lib implies
        (owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) && mayEdit(lib, t, to, make[Target.Doc](d)) &&
          owns(transfer(lib, t, by, d, to), to, d) && transfer(lib, t, by, d, to).shares.contains(ownersEdit(d, to)))) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      ownedBy(lib, what, withWhom) implies (Sharing.unshare(lib, t, by, what, withWhom) === lib)) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
      ownedBy(lib, s.what, s.withWhom) implies (Sharing.share(lib, t, by, s) === lib)))
    .refines(accessFollowsShares)

  val transferContract = Node.claim("The owner of a document, while they may edit it, hands it on to someone who may " +
      "edit it: that person is then its owner, with an edit share of it for good in place of any share of it they " +
      "had. When anyone else asks, or the new owner may not edit it, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      transfer(lib, t, by, d, to) === when(owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) &&
        mayEdit(lib, t, to, make[Target.Doc](d)))(lib
          .updated(_.documents, lib.documents.mapped(doc => when(doc.id === d)(doc.updated(_.owner, to)).otherwise(doc)))
          .updated(_.shares, ownersEdit(d, to) ::
            sharesWithout(lib.shares, make[Target.Doc](d), make[Grantee.Person](to)))).otherwise(lib)))
    .refines(ownersKeepTheirDocuments)

  val transferCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      when(owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) && mayEdit(lib, t, to, make[Target.Doc](d)))(
        lib.updated(_.documents, lib.documents.mapped(doc => when(doc.id === d)(doc.updated(_.owner, to)).otherwise(doc)))
          .updated(_.shares, ownersEdit(d, to) ::
            sharesWithout(lib.shares, make[Target.Doc](d), make[Grantee.Person](to)))).otherwise(lib) }
