package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Ownership.*
import sharing.features.Sharing.sharesWithout

/** Ownership's claims: what its code is proven to do, each refining a branch or the purpose. */
object OwnershipClaims:
  val transferContract = Node.claim("Handing a document on, asked by its owner while they and the new owner may edit " +
      "it, makes the new owner its owner with an edit share for good, in place of any share they had, and otherwise " +
      "changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
      transfer(lib, t, by, d, to) === when(owns(lib, by, d) && mayEdit(lib, t, by, make[Target.Doc](d)) &&
        mayEdit(lib, t, to, make[Target.Doc](d)))(lib
          .updated(_.documents, handedOn(lib, d, to))
          .updated(_.shares, ownersEdit(d, to) ::
            sharesWithout(lib.shares, make[Target.Doc](d), make[Grantee.Person](to)))).otherwise(lib)))
    .refines(onlyTheOwnerHandsOn, newOwnerOwnsForGood)
