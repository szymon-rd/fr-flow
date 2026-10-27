package sharing.ownership

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.ownership.Ownership.*
import sharing.service.Sharing.sharesWithout

/** Ownership's claims: what its code is proven to do, each refining a branch or the purpose. */
object OwnershipClaims:
  val transferContract = Node.claim("The owner of a document, while they may edit it, hands it on to someone who may " +
      "edit it: that person is then its owner, with an edit share of it for good in place of any share of it they " +
      "had. When anyone else asks, or the new owner may not edit it, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      transfer(lib, t, by, d, to) === when(owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) &&
        mayEdit(lib, t, to, make[Target.Doc](d)))(lib
          .updated(_.documents, handedOn(lib, d, to))
          .updated(_.shares, ownersEdit(d, to) ::
            sharesWithout(lib.shares, make[Target.Doc](d), make[Grantee.Person](to)))).otherwise(lib)))
    .refines(ownersKeepTheirDocuments)
