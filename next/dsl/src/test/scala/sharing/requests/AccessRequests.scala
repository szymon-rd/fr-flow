package sharing.requests

import examples.Folds.*
import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.{isPending, reminderDue}
import sharing.time.Run.{after, events, housekeepingWithin}

/** Access requests: a person asks for access to a document or a folder; someone who may edit it approves the request
  * (which makes the share) or declines it; housekeeping reminds the owners of what it is for of a request left
  * unanswered and declines one left too long. Each operation is a function of the library and of the moment.
  */
object AccessRequests:
  val ask = Definition[(Library, BigInt, PersonId, Target, Level) => Library](
    "the library after a person asks for access to a document or folder")
  val approve = Definition[(Library, BigInt, PersonId, PersonId, Target) => Library](
    "the library after someone asks to approve a person's request")
  val decline = Definition[(Library, BigInt, PersonId, PersonId, Target) => Library](
    "the library after someone asks to decline a person's request")
  val chase = Definition[(Library, BigInt) => Library](
    "the library after housekeeping has chased the access requests at a moment")

  /** The branch: what an access request is. */
  val accessRequestsAreAsks = Node.claim("An access request is a person's ask for a document or a folder: asking " +
      "changes nothing shared, offered or kept, so it gives nobody access; only someone who may edit what it is for " +
      "answers it, and approving it, while it is pending, makes the share asked for; and housekeeping declines it " +
      "within one of its periods of its lapsing, and reminds the owners of what it is for within one of its periods " +
      "of its being due a reminder.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      ask(lib, t, p, w, level).shares === lib.shares && ask(lib, t, p, w, level).invitations === lib.invitations &&
        ask(lib, t, p, w, level).documents === lib.documents) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      (approve(lib, t, by, p, w) =!= lib implies
        (mayEdit(lib, t, by, w) && lib.requests.exists(r => r.person === p && r.what === w && isPending(r, t)))) &&
        (decline(lib, t, by, p, w) =!= lib implies mayEdit(lib, t, by, w))) &&
    after(events).library.requests.forall(r => isPending(r, after(events).now - housekeepingWithin) &&
      (r.reminded || !reminderDue(r, after(events).now - housekeepingWithin))))
    .refines(accessFollowsShares)

  /** The requests, less any of `person` for `what`. */
  val requestsWithout = define { (rs: Term[List[AccessRequest]], p: Term[PersonId], w: Term[Target]) =>
    rs.filter(r => !(r.person === p && r.what === w)) }
  /** Whether the library has the document or folder. */
  val holds = define { (lib: Term[Library], w: Term[Target]) =>
    w.on[Target.Doc](d => lib.documents.exists(doc => doc.id === d))
      .on[Target.InFolder](f => lib.folders.exists(x => x.id === f)) }
  /** Whether a request for `w` is for a document: it is of the document, or of a folder around it. */
  val isFor = define { (w: Term[Target], doc: Term[Document]) =>
    w.on[Target.Doc](d => doc.id === d).on[Target.InFolder](f => doc.folders.contains(f)) }

  val askContract = Node.claim("A person asks for access to a document or a folder at a level: the request, made " +
      "now, takes the place of any earlier request of theirs for it. Asking for a document or folder that does not " +
      "exist changes nothing.")(
    forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      ask(lib, t, p, w, level) === when(holds(lib, w))(lib.updated(_.requests,
        make[AccessRequest](p, w, level, t, False) :: requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(accessRequestsAreAsks)

  val askCode = define {
    (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      when(holds(lib, w))(lib.updated(_.requests,
        make[AccessRequest](p, w, level, t, False) :: requestsWithout(lib.requests, p, w))).otherwise(lib) }

  /** The library with the request approved: the share asked for, in place of any, and the request gone. */
  val granted = define { (lib: Term[Library], r: Term[AccessRequest]) =>
    val person = make[Grantee.Person](r.person)
    lib.updated(_.shares, make[Share](r.what, person, r.level, none[BigInt]) :: sharesWithout(lib.shares, r.what, person))
      .updated(_.requests, requestsWithout(lib.requests, r.person, r.what)) }

  val approveContract = Node.claim("Someone who may edit a document or folder approves a person's pending request " +
      "for it: the person then has a share of it at the level asked, for good, in place of any share of it they had, " +
      "and the request goes. Otherwise, or when it is the person's own document (their share of it is the owner's), " +
      "nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      approve(lib, t, by, p, w) ===
        lib.requests.firstWhere(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
          when(mayEdit(lib, t, by, w) && !ownedBy(lib, w, make[Grantee.Person](p)))(granted(lib, r)).otherwise(lib))))
    .refines(accessRequestsAreAsks)

  val approveCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      lib.requests.firstWhere(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
        when(mayEdit(lib, t, by, w) && !ownedBy(lib, w, make[Grantee.Person](p)))(granted(lib, r)).otherwise(lib)) }

  val declineContract = Node.claim("Someone who may edit a document or folder declines a person's request for it: " +
      "the request goes. When anyone else asks, nothing changes.")(
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      decline(lib, t, by, p, w) ===
        when(mayEdit(lib, t, by, w))(lib.updated(_.requests, requestsWithout(lib.requests, p, w))).otherwise(lib)))
    .refines(accessRequestsAreAsks)

  val declineCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      when(mayEdit(lib, t, by, w))(lib.updated(_.requests, requestsWithout(lib.requests, p, w))).otherwise(lib) }

  // ---------------------------------------------------------------------------
  // chasing: what housekeeping does with the requests nobody answered
  // ---------------------------------------------------------------------------

  /** A request as housekeeping leaves it at a moment: reminded, once it is due a reminder. */
  val chased = define { (r: Term[AccessRequest], t: Term[BigInt]) =>
    when(reminderDue(r, t) && !r.reminded)(r.updated(_.reminded, True)).otherwise(r) }
  /** The notices housekeeping sends at a moment: to the requester of each lapsed request, to the owner of each
    * document a request now due a reminder is for (of a folder: of each document in it).
    */
  val chaseNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.requests.filter(r => !isPending(r, t)).mapped(r => make[Notice](r.person, make[Subject.Lapsed](r))) ++
      lib.requests.filter(r => isPending(r, t) && reminderDue(r, t) && !r.reminded).flatMapped(r =>
        lib.documents.filter(doc => isFor(r.what, doc)).mapped(doc => make[Notice](doc.owner, make[Subject.Reminder](r)))) }

  val chaseContract = Node.claim("Housekeeping chases the access requests at a moment: a request no longer pending " +
      "is declined (it goes, and the person is told); a pending one due a reminder, not reminded yet, is marked " +
      "reminded and the owner of each document it is for is told. Everything else stays as it was.")(
    forall((lib: Term[Library], t: Term[BigInt]) => chase(lib, t) === lib
      .updated(_.requests, lib.requests.filter(r => isPending(r, t)).mapped(r => chased(r, t)))
      .updated(_.outbox, lib.outbox ++ chaseNotices(lib, t))))
    .refines(accessRequestsAreAsks)

  val chaseCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.requests, lib.requests.filter(r => isPending(r, t)).mapped(r => chased(r, t)))
      .updated(_.outbox, lib.outbox ++ chaseNotices(lib, t)) }
