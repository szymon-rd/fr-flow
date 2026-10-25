package sharing.requests

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.{isPending, reminderDue}
import sharing.time.Run.{after, events, housekeepingWithin}

/** Access requests: a person asks for access to a document; someone who may edit it approves the request (which makes
  * the share) or declines it; housekeeping reminds the owner of a request left unanswered and declines one left too
  * long. Each method is a function of the library and of the moment.
  */
trait AccessRequests:
  /** The library after `person` asks for access to `doc` at `level`. */
  def ask(library: Library, now: BigInt, person: PersonId, doc: DocumentId, level: Level): Library
  /** The library after `by` approves the request of `person` for `doc`. */
  def approve(library: Library, now: BigInt, by: PersonId, person: PersonId, doc: DocumentId): Library
  /** The library after `by` declines the request of `person` for `doc`. */
  def decline(library: Library, now: BigInt, by: PersonId, person: PersonId, doc: DocumentId): Library
  /** The library after housekeeping has chased the requests at a moment: reminders sent, lapsed requests declined. */
  def chase(library: Library, now: BigInt): Library

/** The access requests' contracts, each with its code. */
object AccessRequests:
  import Demo.*

  val ask = Param[(Library, BigInt, PersonId, DocumentId, Level) => Library]("ask", "the library after a person asks for access to a document")
  val approve = Param[(Library, BigInt, PersonId, PersonId, DocumentId) => Library]("approve", "the library after someone asks to approve a person's request")
  val decline = Param[(Library, BigInt, PersonId, PersonId, DocumentId) => Library]("decline", "the library after someone asks to decline a person's request")
  val chase = Param[(Library, BigInt) => Library]("chase", "the library after housekeeping has chased the access requests at a moment")

  /** The branch: what an access request is. Its parts are the four operations and, below the timed words "pending" and
    * "due a reminder", the deadline by which housekeeping answers a request nobody answered.
    */
  val requestsAreAsks = Node.claim("AccessRequestsAreAsks",
    "An access request is a person's ask: asking changes nothing shared, offered or kept, so it gives nobody access; only someone who may edit the document answers it, and approving it, while it is pending, makes the share asked for; and housekeeping declines it within one of its periods of its lapsing, and reminds the owner of it within one of its periods of its being due a reminder.",
    why = "Q12: a person who has no access asks for it, and an editor decides. Whether a request is still pending, or due a reminder, is left open here (Lifetimes: 7 days and 48 hours); that housekeeping acts on time is RequestsAnsweredOnTime's, with the clock.",
    idea = "Access requests"
  )(forall((lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId], level: Term[Level]) =>
    ask(lib, t, p, d, level).shares === lib.shares && ask(lib, t, p, d, level).invitations === lib.invitations &&
      ask(lib, t, p, d, level).documents === lib.documents) &&
    forall((lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], d: Term[DocumentId]) =>
      (approve(lib, t, by, p, d) =!= lib ==>
        (mayEdit(lib, t, by, Target[Target.Doc](d)) && lib.requests.exists(r => r.person === p && r.doc === d && isPending(r, t)))) &&
      (decline(lib, t, by, p, d) =!= lib ==> mayEdit(lib, t, by, Target[Target.Doc](d)))) &&
    after(events).library.requests.forall(r => isPending(r, after(events).now - housekeepingWithin) &&
      (r.reminded || !reminderDue(r, after(events).now - housekeepingWithin))))
    .under(accessFollowsShares)

  /** The requests, less any of `person` for `doc`. */
  val requestsWithout = define { (rs: Term[List[AccessRequest]], p: Term[PersonId], d: Term[DocumentId]) =>
    rs.filterNot(r => r.person === p && r.doc === d)
  }

  private val catAsks = AccessRequest(cat, plan, Level.View, now - day, false)
  private val withCatAsking = library.copy(requests = List(catAsks))
  private val catViewsPlan = Share(Target.Doc(plan), Grantee.Person(cat), Level.View, None)

  val askContract = Node.contract(ask)("AskContract",
    "A person asks for access to a document at a level: the request, made now, takes the place of any earlier request of theirs for it. Asking for a document that does not exist changes nothing.",
    why = "Q12: anyone named in the library may ask; one request per person and document, so asking again renews it.",
    idea = "Access requests"
  )((lib, t, p, d, level, result) =>
    result === lib.documents.exists(doc => doc.id === d).fold(
      lib.copy((requests = AccessRequest(p, d, level, t, False) :: requestsWithout(lib.requests, p, d))), lib))
    .under(requestsAreAsks)
    .examples()(
      expect(library, now - day, cat, plan, Level.View, withCatAsking, "Cat asks to view the plan"),
      expect(library, now, cat, DocumentId("nowhere"), Level.View, library, "no such document: nothing changes"),
      reject(library, now, cat, plan, Level.View, library.copy(shares = catViewsPlan :: library.shares), "asking gives no access"))

  val askCode = define { (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], d: Term[DocumentId], level: Term[Level]) =>
    lib.documents.exists(doc => doc.id === d).fold(
      lib.copy((requests = AccessRequest(p, d, level, t, False) :: requestsWithout(lib.requests, p, d))), lib)
  }

  val approveContract = Node.contract(approve)("ApproveContract",
    "Someone who may edit a document approves a person's pending request for it: the person then has a share of it at the level asked, for good, in place of any share of it they had, and the request goes. Otherwise nothing changes.",
    why = "Q12: approving makes the share; a request that has lapsed can no longer be approved, the person asks again.",
    idea = "Access requests"
  )((lib, t, by, p, d, result) =>
    result === lib.requests.find(r => r.person === p && r.doc === d && isPending(r, t)).fold(lib)(r =>
      mayEdit(lib, t, by, Target[Target.Doc](d)).fold(
        lib.copy((shares = Share(Target[Target.Doc](d), Grantee[Grantee.Person](p), r.level, none[BigInt]) ::
          sharesWithout(lib.shares, Target[Target.Doc](d), Grantee[Grantee.Person](p)),
          requests = requestsWithout(lib.requests, p, d))), lib)))
    .under(requestsAreAsks)
    .examples()(
      expect(withCatAsking, now, ann, cat, plan, library.copy(shares = catViewsPlan :: library.shares), "Ann approves: Cat may view the plan"),
      expect(withCatAsking, now, bob, cat, plan, withCatAsking, "Bob may not edit the plan: the request stays"),
      expect(withCatAsking, now + 7 * day, ann, cat, plan, withCatAsking, "eight days on the request has lapsed"),
      reject(withCatAsking, now, bob, cat, plan, library.copy(shares = catViewsPlan :: library.shares), "only an editor approves"))

  val approveCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], d: Term[DocumentId]) =>
    lib.requests.find(r => r.person === p && r.doc === d && isPending(r, t)).fold(lib)(r =>
      mayEdit(lib, t, by, Target[Target.Doc](d)).fold(
        lib.copy((shares = Share(Target[Target.Doc](d), Grantee[Grantee.Person](p), r.level, none[BigInt]) ::
          sharesWithout(lib.shares, Target[Target.Doc](d), Grantee[Grantee.Person](p)),
          requests = requestsWithout(lib.requests, p, d))), lib))
  }

  val declineContract = Node.contract(decline)("DeclineContract",
    "Someone who may edit a document declines a person's request for it: the request goes. When anyone else asks, nothing changes.",
    why = "Q12: an editor may say no; the person may ask again.",
    idea = "Access requests"
  )((lib, t, by, p, d, result) =>
    result === mayEdit(lib, t, by, Target[Target.Doc](d)).fold(lib.copy((requests = requestsWithout(lib.requests, p, d))), lib))
    .under(requestsAreAsks)
    .examples()(
      expect(withCatAsking, now, ann, cat, plan, library, "Ann declines Cat's request"),
      expect(withCatAsking, now, bob, cat, plan, withCatAsking, "Bob may not edit the plan: the request stays"),
      reject(withCatAsking, now, bob, cat, plan, library, "only an editor declines"))

  val declineCode = define { (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], d: Term[DocumentId]) =>
    mayEdit(lib, t, by, Target[Target.Doc](d)).fold(lib.copy((requests = requestsWithout(lib.requests, p, d))), lib)
  }

  // ---------------------------------------------------------------------------
  // chasing: what housekeeping does with the requests nobody answered
  // ---------------------------------------------------------------------------

  /** A request as housekeeping leaves it at a moment: reminded, once it is due a reminder. */
  val chased = define { (r: Term[AccessRequest], t: Term[BigInt]) => (reminderDue(r, t) && !r.reminded).fold(r.copy((reminded = True)), r) }
  /** The notices housekeeping sends at a moment: to the requester of each lapsed request, to the owner of the document
    * of each request now due a reminder.
    */
  val chaseNotices = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.requests.filter(r => !isPending(r, t)).map(r => Notice(r.person, Subject[Subject.Lapsed](r))) ++
      lib.requests.filter(r => isPending(r, t) && reminderDue(r, t) && !r.reminded)
        .flatMap(r => lib.documents.filter(doc => doc.id === r.doc).map(doc => Notice(doc.owner, Subject[Subject.Reminder](r))))
  }

  private val catAskedLongAgo = AccessRequest(cat, plan, Level.View, now - 3 * day, false)

  val chaseContract = Node.contract(chase)("ChaseContract",
    "Housekeeping chases the access requests at a moment: a request no longer pending is declined (it goes, and the person is told); a pending one due a reminder, not reminded yet, is marked reminded and its document's owner is told. Everything else stays as it was.",
    why = "Q12: a reminder after 48 hours, once; declined automatically after 7 days. The notices go to the outbox with the change, so they are sent once it is saved (Q13).",
    idea = "Access requests"
  )((lib, t, result) =>
    result === lib.copy((requests = lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)),
      outbox = lib.outbox ++ chaseNotices(lib, t))))
    .under(requestsAreAsks)
    .examples()(
      expect(withCatAsking, now, withCatAsking, "asked a day ago: nothing to do"),
      expect(library.copy(requests = List(catAskedLongAgo)), now,
        library.copy(requests = List(catAskedLongAgo.copy(reminded = true)), outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo)))),
        "asked three days ago: Ann, the plan's owner, is reminded"),
      expect(withCatAsking, now + 7 * day, library.copy(outbox = List(Notice(cat, Subject.Lapsed(catAsks)))),
        "eight days on: declined, and Cat is told"),
      reject(library.copy(requests = List(catAskedLongAgo.copy(reminded = true))), now,
        library.copy(requests = List(catAskedLongAgo.copy(reminded = true)), outbox = List(Notice(ann, Subject.Reminder(catAskedLongAgo)))),
        "a request is reminded of once"))

  val chaseCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.copy((requests = lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)), outbox = lib.outbox ++ chaseNotices(lib, t)))
  }
