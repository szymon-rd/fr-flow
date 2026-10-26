package sharing.requests

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.{isPending, reminderDue}
import sharing.time.Run.{after, events, housekeepingWithin}

/** Access requests: a person asks for access to a document or a folder; someone who may edit it approves the request
  * (which makes the share) or declines it; housekeeping reminds the owners of what it is for of a request left
  * unanswered and declines one left too long. Each method is a function of the library and of the moment.
  */
trait AccessRequests:
  /** The library after `person` asks for access to `what` (a document or a folder) at `level`. */
  def ask(library: Library, now: BigInt, person: PersonId, what: Target, level: Level): Library
  /** The library after `by` approves the request of `person` for `what`. */
  def approve(library: Library, now: BigInt, by: PersonId, person: PersonId, what: Target): Library
  /** The library after `by` declines the request of `person` for `what`. */
  def decline(library: Library, now: BigInt, by: PersonId, person: PersonId, what: Target): Library
  /** The library after housekeeping has chased the requests at a moment: reminders sent, lapsed requests declined. */
  def chase(library: Library, now: BigInt): Library

/** The access requests' contracts, each with its code. */
object AccessRequests:
  import Demo.*

  val ask = Param[(Library, BigInt, PersonId, Target, Level) => Library]("the library after a person asks for access to a document or folder")
  val approve = Param[(Library, BigInt, PersonId, PersonId, Target) => Library]("the library after someone asks to approve a person's request")
  val decline = Param[(Library, BigInt, PersonId, PersonId, Target) => Library]("the library after someone asks to decline a person's request")
  val chase = Param[(Library, BigInt) => Library]("the library after housekeeping has chased the access requests at a moment")

  /** The branch: what an access request is. Its parts are the four operations and, below the timed words "pending" and
    * "due a reminder", the deadline by which housekeeping answers a request nobody answered.
    */
  val accessRequestsAreAsks = Node.claim("An access request is a person's ask for a document or a folder: asking changes nothing shared, offered or kept, so it gives nobody access; only someone who may edit what it is for answers it, and approving it, while it is pending, makes the share asked for; and housekeeping declines it within one of its periods of its lapsing, and reminds the owners of what it is for within one of its periods of its being due a reminder.",
    why = "Q12: a person who has no access asks for it, and an editor decides; for a document or a folder. Whether a request is still pending, or due a reminder, is left open here (Lifetimes: 7 days and 48 hours); that housekeeping acts on time is RequestsAnsweredOnTime's, with the clock.",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
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
    rs.filterNot(r => r.person === p && r.what === w)
  }
  /** Whether the library has the document or folder. */
  val holds = define { (lib: Term[Library], w: Term[Target]) =>
    w.on[Target.Doc](d => lib.documents.exists(doc => doc.id === d)).on[Target.InFolder](f => lib.folders.exists(x => x.id === f))
  }
  /** Whether a request for `w` is for a document: it is of the document, or of a folder around it. */
  val isFor = define { (w: Term[Target], doc: Term[Document]) =>
    w.on[Target.Doc](d => doc.id === d).on[Target.InFolder](f => doc.folders.contains(f))
  }

  private val catAsks = AccessRequest(cat, Target.Doc(plan), Level.View, now - day, false)
  private val catAsksForReports = AccessRequest(cat, Target.InFolder(reports), Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)
  private val annAsks = library.copy(requests = List(AccessRequest(ann, Target.Doc(plan), Level.View, now - day, false)))

  val askContract = Node.contract("A person asks for access to a document or a folder at a level: the request, made now, takes the place of any earlier request of theirs for it. Asking for a document or folder that does not exist changes nothing.",
    why = "Q12: anyone named in the library may ask, for a document or a folder; one request per person and document or folder, so asking again renews it.",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    ask(lib, t, p, w, level) === holds(lib, w).fold(
      lib.copy((requests = AccessRequest(p, w, level, t, False) :: requestsWithout(lib.requests, p, w))), lib)))
    .refines(accessRequestsAreAsks)
    .examples()(
      allows(library, now - day, cat, Target.Doc(plan), Level.View, withCatAsking, "Cat asks to view the plan"),
      allows(library, now - day, cat, Target.InFolder(reports), Level.View, library.copy(requests = List(catAsksForReports)),
        "Cat asks to view the reports folder"),
      allows(library, now, cat, Target.Doc(DocumentId("nowhere")), Level.View, library, "no such document: nothing changes"),
      forbids(library, now, cat, Target.Doc(plan), Level.View, library.copy(shares = catViewsPlan :: library.shares), "asking gives no access"))

  val askCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
    holds(lib, w).fold(
      lib.copy((requests = AccessRequest(p, w, level, t, False) :: requestsWithout(lib.requests, p, w))), lib)
  }

  val approveContract = Node.contract("Someone who may edit a document or folder approves a person's pending request for it: the person then has a share of it at the level asked, for good, in place of any share of it they had, and the request goes. Otherwise, or when it is the person's own document (their share of it is the owner's), nothing changes.",
    why = "Q12: approving makes the share; a request that has lapsed can no longer be approved, the person asks again. Q14: nothing replaces an owner's share of their own document.",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    approve(lib, t, by, p, w) === lib.requests.find(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
      (mayEdit(lib, t, by, w) && !ownedBy(lib, w, Grantee[Grantee.Person](p))).fold(
        lib.copy((shares = Share(w, Grantee[Grantee.Person](p), r.level, none[BigInt]) ::
          sharesWithout(lib.shares, w, Grantee[Grantee.Person](p)),
          requests = requestsWithout(lib.requests, p, w))), lib))))
    .refines(accessRequestsAreAsks)
    .examples()(
      allows(withCatAsking, now, ann, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares), "Ann approves: Cat may view the plan"),
      allows(withCatAsking, now, bob, cat, Target.Doc(plan), withCatAsking, "Bob may not edit the plan: the request stays"),
      allows(withCatAsking, now + 7 * day, ann, cat, Target.Doc(plan), withCatAsking, "eight days on the request has lapsed"),
      allows(annAsks, now, ann, ann, Target.Doc(plan), annAsks, "Ann owns the plan: her request for view of it changes nothing"),
      forbids(withCatAsking, now, bob, cat, Target.Doc(plan), library.copy(shares = catViewsPlan :: library.shares), "only an editor approves"))

  val approveCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    lib.requests.find(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
      (mayEdit(lib, t, by, w) && !ownedBy(lib, w, Grantee[Grantee.Person](p))).fold(
        lib.copy((shares = Share(w, Grantee[Grantee.Person](p), r.level, none[BigInt]) ::
          sharesWithout(lib.shares, w, Grantee[Grantee.Person](p)),
          requests = requestsWithout(lib.requests, p, w))), lib))
  }

  val declineContract = Node.contract("Someone who may edit a document or folder declines a person's request for it: the request goes. When anyone else asks, nothing changes.",
    why = "Q12: an editor may say no; the person may ask again.",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    decline(lib, t, by, p, w) === mayEdit(lib, t, by, w).fold(lib.copy((requests = requestsWithout(lib.requests, p, w))), lib)))
    .refines(accessRequestsAreAsks)
    .examples()(
      allows(withCatAsking, now, ann, cat, Target.Doc(plan), library, "Ann declines Cat's request"),
      allows(withCatAsking, now, bob, cat, Target.Doc(plan), withCatAsking, "Bob may not edit the plan: the request stays"),
      forbids(withCatAsking, now, bob, cat, Target.Doc(plan), library, "only an editor declines"))

  val declineCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
    mayEdit(lib, t, by, w).fold(lib.copy((requests = requestsWithout(lib.requests, p, w))), lib)
  }

  // ---------------------------------------------------------------------------
  // chasing: what housekeeping does with the requests nobody answered
  // ---------------------------------------------------------------------------

  /** A request as housekeeping leaves it at a moment: reminded, once it is due a reminder. */
  val chased = define { (r: Term[AccessRequest], t: Term[BigInt]) => (reminderDue(r, t) && !r.reminded).fold(r.copy((reminded = True)), r) }
  /** The notices housekeeping sends at a moment: to the requester of each lapsed request, to the owner of each document
    * a request now due a reminder is for (of a folder: of each document in it).
    */
  val chaseNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.requests.filter(r => !isPending(r, t)).map(r => Notice(r.person, Subject[Subject.Lapsed](r))) ++
      lib.requests.filter(r => isPending(r, t) && reminderDue(r, t) && !r.reminded)
        .flatMap(r => lib.documents.filter(doc => isFor(r.what, doc)).map(doc => Notice(doc.owner, Subject[Subject.Reminder](r))))
  }

  private val catAskedLongAgo = AccessRequest(cat, Target.Doc(plan), Level.View, now - 3 * day, false)

  val chaseContract = Node.contract("Housekeeping chases the access requests at a moment: a request no longer pending is declined (it goes, and the person is told); a pending one due a reminder, not reminded yet, is marked reminded and the owner of each document it is for is told. Everything else stays as it was.",
    why = "Q12: a reminder after 48 hours, once; declined automatically after 7 days. The notices go to the outbox with the change, so they are sent once it is saved (Q13).",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt]) =>
    chase(lib, t) === lib.copy((requests = lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)),
      outbox = lib.outbox ++ chaseNotices(lib, t)))))
    .refines(accessRequestsAreAsks)
    .examples()(
      allows(withCatAsking, now, withCatAsking, "asked a day ago: nothing to do"),
      allows(library.copy(requests = List(catAskedLongAgo)), now,
        library.copy(requests = List(catAskedLongAgo.copy(reminded = true)), outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo)))),
        "asked three days ago: Ann, the plan's owner, is reminded"),
      allows(withCatAsking, now + 7 * day, library.copy(outbox = List(Notice(cat, Subject.Lapsed(catAsks)))),
        "eight days on: declined, and Cat is told"),
      forbids(library.copy(requests = List(catAskedLongAgo.copy(reminded = true))), now,
        library.copy(requests = List(catAskedLongAgo.copy(reminded = true)), outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo)))),
        "a request is reminded of once"))

  val chaseCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.copy((requests = lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)), outbox = lib.outbox ++ chaseNotices(lib, t)))
  }
