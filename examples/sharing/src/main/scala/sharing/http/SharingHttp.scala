package sharing.http

import frflow.*
import sharing.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.invitations.Invitations
import sharing.notifications.{MailerModel, Notifications}
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.store.LibraryModel
import sharing.store.LibraryStore.store
import sharing.time.Lifetimes.{isOpen, isPending}
import sharing.trash.Trash

/** The service as clients reach it: a request, answered at the time the clock gives from the library the store keeps,
  * and the store left holding the library the request leads to. `HttpCodec` turns HTTP into requests and answers into
  * HTTP; `Server` serves it.
  */
trait SharingHttp:
  def handle(request: Request): Answer

/** The handling of a request and its contract. */
object SharingHttp:
  import Demo.*

  val handle = Param[Request => Flow[Answer]]("a request handled on the store and the clock: the answer, the store left holding the change")

  /** The library a request leads to at a moment: the operation's change for a change; the same library for a question. */
  val afterRequest = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((_, _) => lib)
      .on[Request.Share]((by, what, withWhom, level, until) => Sharing.share(lib, t, by, Share(what, withWhom, level, until)))
      .on[Request.Unshare]((by, what, withWhom) => Sharing.unshare(lib, t, by, what, withWhom))
      .on[Request.Move]((by, d, into) => Sharing.move(lib, t, by, d, into))
      .on[Request.Invite]((by, to, what, level) => Invitations.invite(lib, t, by, to, what, level))
      .on[Request.Accept]((p, what) => Invitations.accept(lib, t, p, what))
      .on[Request.Withdraw]((by, to, what) => Invitations.withdraw(lib, t, by, to, what))
      .on[Request.Trash]((by, d) => Trash.trash(lib, t, by, d))
      .on[Request.Restore]((by, d) => Trash.restore(lib, t, by, d))
      .on[Request.Ask]((p, d, level) => AccessRequests.ask(lib, t, p, d, level))
      .on[Request.Approve]((by, p, d) => AccessRequests.approve(lib, t, by, p, d))
      .on[Request.Decline]((by, p, d) => AccessRequests.decline(lib, t, by, p, d))
      .on[Request.Transfer]((by, d, to) => Ownership.transfer(lib, t, by, d, to))
  }

  /** The library a request leaves in the store: when it changes the library, the change, recorded in the log and
    * announced in the outbox, all in the one save.
    */
  val served = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    let(afterRequest(lib, t, r))(next => (next =!= lib).fold(
      Notifications.announce(Audit.record(next, t, Change[Change.Made](r)), lib, r, Entry(next.log.length, t, Change[Change.Made](r))), lib))
  }

  /** Done when the asker may make the change, refused otherwise. */
  private def allowedWhen(c: Term[Boolean]): Term[Answer] = c.fold(Answer.Done: Term[Answer], Answer.Refused: Term[Answer])

  /** The answer to a request at a moment: the person's access to the document; for a change, whether it may be made. */
  val answerTo = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((p, d) => Answer[Answer.Access](Sharing.access(lib, t, p, d)))
      .on[Request.Share]((by, what, withWhom, _, _) => allowedWhen(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)))
      .on[Request.Unshare]((by, what, withWhom) => allowedWhen(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)))
      .on[Request.Move]((by, d, into) => allowedWhen(Sharing.mayMove(lib, t, by, d, into)))
      .on[Request.Invite]((by, _, what, _) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Accept]((p, what) => allowedWhen(lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t)) &&
        !ownedBy(lib, what, Grantee[Grantee.Person](p))))
      .on[Request.Withdraw]((by, _, what) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Trash]((by, d) => allowedWhen(mayEdit(lib, t, by, Target[Target.Doc](d))))
      .on[Request.Restore]((by, d) => allowedWhen(Trash.mayRestore(lib, t, by, d)))
      .on[Request.Ask]((_, w, _) => allowedWhen(AccessRequests.holds(lib, w)))
      .on[Request.Approve]((by, p, w) => allowedWhen(mayEdit(lib, t, by, w) && !ownedBy(lib, w, Grantee[Grantee.Person](p)) &&
        lib.requests.exists(q => q.person === p && q.what === w && isPending(q, t))))
      .on[Request.Decline]((by, _, w) => allowedWhen(mayEdit(lib, t, by, w)))
      .on[Request.Transfer]((by, d, to) => allowedWhen(Ownership.owns(lib, by, d) && mayEdit(lib, t, by, Target[Target.Doc](d)) &&
        mayEdit(lib, t, to, Target[Target.Doc](d))))
  }

  private val shareWithBob = Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None)
  private val bobViewsPlan = library.copy(shares = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None) :: library.shares,
    log = List(Entry(0, now, Change.Made(shareWithBob))))
  private def at(l: Library) = World(LibraryModel -> l, MailerModel -> Map.empty[PersonId, List[Notice]], ClockModel -> ClockState(now, Nil))

  val handleContract = Node.contract(handle)("A request is answered at the time the clock gives, from the library the store holds, and leaves the store holding the library it leads to: a question is answered with the person's access and changes nothing; a change is made as its operation makes it, recorded in the log and announced in the outbox in the same save, and answered done when it may be made and refused otherwise. Handling does not move the clock. A request the store fails changes nothing.",
    why = "This is the service as a client sees it, in the store's and the clock's terms (LibraryKept, ClockKept). What the answers and changes are is the operations' (their contracts); what this adds is that each request reads the library the last one left and the clock once, and leaves the library it leads to, so a client's next request sees its change. One save per request is one transaction: Q16, a store failure mid-request changes nothing, proven for every pattern of the store's failures; the server answers it 503 (ServerWiring).",
    idea = "Failures"
  )((r, result, before, after) =>
    after(LibraryModel) === served(before(LibraryModel), before(ClockModel).now, r) && after(ClockModel) === before(ClockModel) &&
      after(MailerModel) === before(MailerModel) && result === answerTo(before(LibraryModel), before(ClockModel).now, r))
    .failsChangingNothing[Failure]
    .refines(accessFollowsShares)
    .examples()(
      allows(Request.Access(bob, q3Report), at(library), Answer.Access(Some(Level.View)), at(library),
        "Bob's team may view the reports folder: Bob can view the Q3 report, and nothing changes"),
      allows(shareWithBob, at(library), Answer.Done,
        at(bobViewsPlan), "Ann shares the plan with Bob: the store holds the new share, and its entry in the log"),
      allows(shareWithBob, at(library).failing(false, true), Failed(Failure.StoreUnavailable), at(library),
        "the store fails as the share is saved: nothing changes"),
      forbids(shareWithBob, at(library).failing(false, true), Failed(Failure.StoreUnavailable), at(bobViewsPlan),
        "a request the store fails is never half kept"),
      allows(Request.Share(bob, Target.Doc(plan), Grantee.Person(bob), Level.Edit, None), at(library), Answer.Refused,
        at(library), "Bob may not edit the plan: refused, and the store keeps the library"),
      forbids(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None), at(library), Answer.Done,
        at(library), "a change answered done is kept"),
      forbids(Request.Access(cat, plan), at(library), Answer.Access(Some(Level.View)), at(library),
        "Cat has no access to the plan"))

  /** The handling, one transaction (Q18): the time, the library, the one the request leaves kept when it differs, the
    * answer. HandleContract is proven of it, on the store's and the clock's models, for every pattern of the store's
    * failures; that requests at once leave what one after the other leaves is the store's transactions' (Transactions).
    */
  def handleRequest(r: Term[Request]): Flow[Answer] =
    Flow.atomically(
      for
        t    <- Flow.now
        lib  <- store.load
        next = served(lib, t, r)
        _    <- Flow.whenA(next =!= lib)(store.save(next))
      yield answerTo(lib, t, r))
