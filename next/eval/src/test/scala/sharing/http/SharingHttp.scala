package sharing.http

import frflow.*
import sharing.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.invitations.Invitations
import sharing.notifications.Notifications
import sharing.notifications.Notifications.mailerModel
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.store.LibraryStore
import sharing.store.LibraryStore.{libraryModel, oneTransactionAtATime}
import sharing.time.ClockKept.{clockAlone, clockModel}
import sharing.time.Lifetimes.{isOpen, isPending}
import sharing.trash.Trash

// The service as clients reach it: a request, answered at the time the clock gives from the library the store keeps,
// and the store left holding the library the request leads to. Its two matches over every request, with a `let` and
// the folds, are the compile-time spike's (ARCHITECTURE.md 10.3): this file compiles in every build.

/** The handling of a request and its claim. */
object SharingHttp:
  val handle = Definition[Request => Program[Answer]](
    "a request handled on the store and the clock: the answer, the store left holding the change")

  /** The library a request leads to at a moment: the operation's change for a change; the same library for a
    * question.
    */
  val afterRequest = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((_, _) => lib)
      .on[Request.Share]((by, what, withWhom, level, until) =>
        Sharing.share(lib, t, by, make[Share](what, withWhom, level, until)))
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
      .on[Request.Transfer]((by, d, to) => Ownership.transfer(lib, t, by, d, to)) }

  /** The library a request leaves in the store: when it changes the library, the change, recorded in the log and
    * announced in the outbox, all in the one save.
    */
  val served = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    let(afterRequest(lib, t, r))(next => when(next =!= lib)(Notifications.announce(
      Audit.record(next, t, make[Change.Made](r)), lib, r, make[Entry](next.log.length, t, make[Change.Made](r))))
      .otherwise(lib)) }

  /** Done when the asker may make the change, refused otherwise. */
  private def allowedWhen(c: Term[Boolean]): Term[Answer] = when(c)(Answer.Done: Term[Answer]).otherwise(Answer.Refused)

  /** The answer to a request at a moment: the person's access to the document; for a change, whether it may be
    * made.
    */
  val answerTo = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((p, d) => make[Answer.Access](Sharing.access(lib, t, p, d)))
      .on[Request.Share]((by, what, withWhom, _, _) =>
        allowedWhen(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)))
      .on[Request.Unshare]((by, what, withWhom) =>
        allowedWhen(mayEdit(lib, t, by, what) && !ownedBy(lib, what, withWhom)))
      .on[Request.Move]((by, d, into) => allowedWhen(Sharing.mayMove(lib, t, by, d, into)))
      .on[Request.Invite]((by, _, what, _) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Accept]((p, what) => allowedWhen(
        lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t)) &&
          !ownedBy(lib, what, make[Grantee.Person](p))))
      .on[Request.Withdraw]((by, _, what) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Trash]((by, d) => allowedWhen(mayEdit(lib, t, by, make[Target.Doc](d))))
      .on[Request.Restore]((by, d) => allowedWhen(Trash.mayRestore(lib, t, by, d)))
      .on[Request.Ask]((_, w, _) => allowedWhen(AccessRequests.holds(lib, w)))
      .on[Request.Approve]((by, p, w) => allowedWhen(mayEdit(lib, t, by, w) &&
        !ownedBy(lib, w, make[Grantee.Person](p)) &&
        lib.requests.exists(q => q.person === p && q.what === w && isPending(q, t))))
      .on[Request.Decline]((by, _, w) => allowedWhen(mayEdit(lib, t, by, w)))
      .on[Request.Transfer]((by, d, to) => allowedWhen(Ownership.owns(lib, by, d) &&
        mayEdit(lib, t, by, make[Target.Doc](d)) && mayEdit(lib, t, to, make[Target.Doc](d)))) }

  val handleContract = Node.claim("A request is answered at the time the clock gives, from the library the store " +
      "holds, and leaves the store holding the library it leads to: a question is answered with the person's access " +
      "and changes nothing; a change is made as its operation makes it, recorded in the log and announced in the " +
      "outbox in the same save, and answered done when it may be made and refused otherwise. Handling does not move " +
      "the clock. A request the store fails changes nothing.")(
    forall((r: Term[Request], before: Term[World]) => handle(r).from(before) { (result, after) =>
      libraryModel.in(after) === served(libraryModel.in(before), clockModel.in(before), r) &&
        clockModel.in(after) === clockModel.in(before) && mailerModel.in(after) === mailerModel.in(before) &&
        result === answerTo(libraryModel.in(before), clockModel.in(before), r) }
      .failsChangingNothing[Failure]))
    .refines(accessFollowsShares)
    .assuming(oneTransactionAtATime, clockAlone)

  /** The handling, one transaction: the time, the library, the one the request leaves kept when it differs, the
    * answer.
    */
  object Handling:
    def run[F[_]](r: Term[Request])(using f: Flow[F]): F[Term[Answer]] =
      f.atomically(f.flatMap(Clock.now)(t => f.flatMap(LibraryStore.load) { lib =>
        val next = served(lib, t, r)
        f.as(f.cond(next =!= lib)(LibraryStore.save(next), f.unit), answerTo(lib, t, r)) }))

  val handleRequest = program { (r: Term[Request]) => Handling.run[Recorded](r) }
