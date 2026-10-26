package sharing.ownership

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing
import sharing.service.Sharing.sharesWithout

/** Ownership: every document has one owner, who alone hands it on. The owner's own shares of their document are
  * theirs: nobody unshares or replaces them (UnshareContract, ShareContract). A function of the library and of the moment.
  */
trait Ownership:
  /** The library after `by` hands `doc` on to `to`. */
  def transfer(library: Library, now: BigInt, by: PersonId, doc: DocumentId, to: PersonId): Library

/** Ownership's contract, its code, and the branch it is part of. */
object Ownership:
  import Demo.*

  val transfer = Param[(Library, BigInt, PersonId, DocumentId, PersonId) => Library]("the library after someone asks to hand a document on")

  /** Whether `by` owns the document. */
  val owns = define { (lib: Term[Library], by: Term[PersonId], d: Term[DocumentId]) =>
    lib.documents.exists(doc => doc.id === d && doc.owner === by)
  }

  /** The branch: what owning a document means. Its parts are the transfer, and unsharing (which leaves an owner's
    * shares alone).
    */
  val ownersKeepTheirDocuments = Node.claim("A document has one owner. Only its owner, while they may edit it, hands it on, and only to someone who may edit it, who then has an edit share of it for good; and nobody unshares or replaces an owner's shares of their own document. An owner's share is with them in person, not through a team, so leaving a team never takes their documents from them.",
    why = "Q14: every document has exactly one owner, its creator; only the owner transfers it, to someone who may edit it; the owner always may edit; an owner leaving a team keeps their documents; the owner's share cannot be unshared or expire. Exactly one owner is the type: a document names its owner.",
    idea = "Ownership"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    transfer(lib, t, by, d, to) =!= lib implies
      (owns(lib, by, d) && mayEdit(lib, t, by, Target[Target.Doc](d)) && mayEdit(lib, t, to, Target[Target.Doc](d)) &&
        owns(transfer(lib, t, by, d, to), to, d) &&
        transfer(lib, t, by, d, to).shares.contains(Share(Target[Target.Doc](d), Grantee[Grantee.Person](to), Level.Edit, none[BigInt])))) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], what: Term[Target], withWhom: Term[Grantee]) =>
      ownedBy(lib, what, withWhom) implies (Sharing.unshare(lib, t, by, what, withWhom) === lib)) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], s: Term[Share]) =>
      ownedBy(lib, s.what, s.withWhom) implies (Sharing.share(lib, t, by, s) === lib)))
    .refines(accessFollowsShares)

  private val bobEditsPlan = Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None)
  private val bobMayEdit = library.copy(shares = bobEditsPlan :: library.shares)

  val transferContract = Node.contract(transfer)("The owner of a document, while they may edit it, hands it on to someone who may edit it: that person is then its owner, with an edit share of it for good in place of any share of it they had. When anyone else asks, or the new owner may not edit it, nothing changes.",
    why = "Q14: only the owner transfers a document, to someone who may edit it; the new owner's share makes sure they always may edit it.",
    idea = "Ownership"
  )((lib, t, by, d, to, result) =>
    result === (owns(lib, by, d) && mayEdit(lib, t, by, Target[Target.Doc](d)) && mayEdit(lib, t, to, Target[Target.Doc](d))).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((owner = to)), doc)),
        shares = Share(Target[Target.Doc](d), Grantee[Grantee.Person](to), Level.Edit, none[BigInt]) ::
          sharesWithout(lib.shares, Target[Target.Doc](d), Grantee[Grantee.Person](to)))), lib))
    .refines(ownersKeepTheirDocuments)
    .examples()(
      allows(bobMayEdit, now, ann, plan, bob,
        library.copy(documents = List(planDoc.copy(owner = bob), q3ReportDoc), shares = bobEditsPlan :: library.shares),
        "Ann hands the plan on to Bob, who may edit it"),
      allows(library, now, ann, plan, bob, library, "Bob may not edit the plan: Ann keeps it"),
      allows(bobMayEdit, now, bob, plan, cat, bobMayEdit, "Bob does not own the plan"),
      forbids(bobMayEdit, now, bob, plan, bob,
        bobMayEdit.copy(documents = List(planDoc.copy(owner = bob), q3ReportDoc)), "only the owner hands a document on"))

  val transferCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], d: Term[DocumentId], to: Term[PersonId]) =>
    (owns(lib, by, d) && mayEdit(lib, t, by, Target[Target.Doc](d)) && mayEdit(lib, t, to, Target[Target.Doc](d))).fold(
      lib.copy((documents = lib.documents.map(doc => (doc.id === d).fold(doc.copy((owner = to)), doc)),
        shares = Share(Target[Target.Doc](d), Grantee[Grantee.Person](to), Level.Edit, none[BigInt]) ::
          sharesWithout(lib.shares, Target[Target.Doc](d), Grantee[Grantee.Person](to)))), lib)
  }
