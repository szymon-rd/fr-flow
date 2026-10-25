package sharing.http

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.invitations.Invitations
import sharing.service.Sharing
import sharing.store.LibraryModel
import sharing.store.LibraryStore.store
import sharing.time.Lifetimes.isOpen
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

  val handle = Param[Request => Flow[Answer]]("handle", "a request handled on the store and the clock: the answer, the store left holding the change")

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
  }

  /** Done when the asker may make the change, refused otherwise. */
  private def allowedWhen(c: Term[Boolean]): Term[Answer] = c.fold(Answer.Done: Term[Answer], Answer.Refused: Term[Answer])

  /** The answer to a request at a moment: the person's access to the document; for a change, whether it may be made. */
  val answerTo = define { (lib: Term[Library], t: Term[BigInt], r: Term[Request]) =>
    r.on[Request.Access]((p, d) => Answer[Answer.Access](Sharing.access(lib, t, p, d)))
      .on[Request.Share]((by, what, _, _, _) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Unshare]((by, what, _) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Move]((by, d, into) => allowedWhen(Sharing.mayMove(lib, t, by, d, into)))
      .on[Request.Invite]((by, _, what, _) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Accept]((p, what) => allowedWhen(lib.invitations.exists(i => i.to === p && i.what === what && isOpen(i, t))))
      .on[Request.Withdraw]((by, _, what) => allowedWhen(mayEdit(lib, t, by, what)))
      .on[Request.Trash]((by, d) => allowedWhen(mayEdit(lib, t, by, Target[Target.Doc](d))))
      .on[Request.Restore]((by, d) => allowedWhen(Trash.mayRestore(lib, t, by, d)))
  }

  private val bobViewsPlan = library.copy(shares = Share(Target.Doc(plan), Grantee.Person(bob), Level.View, None) :: library.shares)
  private def at(l: Library) = World(LibraryModel -> l, ClockModel -> ClockState(now, Nil))

  val handleContract = Node.contract(handle)("HandleContract",
    "A request is answered at the time the clock gives, from the library the store holds, and leaves the store holding the library it leads to: a question is answered with the person's access and changes nothing; a change is made as its operation makes it, and answered done when it may be made and refused otherwise. Handling does not move the clock.",
    why = "This is the service as a client sees it, in the store's and the clock's terms (LibraryKept, ClockKept). What the answers and changes are is the operations' (their contracts); what this adds is that each request reads the library the last one left and the clock once, and leaves the library it leads to, so a client's next request sees its change.",
    idea = "Serving"
  )((r, result, before, after) =>
    after(LibraryModel) === afterRequest(before(LibraryModel), before(ClockModel).now, r) && after(ClockModel) === before(ClockModel) &&
      result === answerTo(before(LibraryModel), before(ClockModel).now, r))
    .under(accessFollowsShares)
    .examples()(
      expect(Request.Access(bob, q3Report), at(library), Answer.Access(Some(Level.View)), at(library),
        "Bob's team may view the reports folder: Bob can view the Q3 report, and nothing changes"),
      expect(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None), at(library), Answer.Done,
        at(bobViewsPlan), "Ann shares the plan with Bob: the store holds the new share"),
      expect(Request.Share(bob, Target.Doc(plan), Grantee.Person(bob), Level.Edit, None), at(library), Answer.Refused,
        at(library), "Bob may not edit the plan: refused, and the store keeps the library"),
      reject(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, None), at(library), Answer.Done,
        at(library), "a change answered done is kept"),
      reject(Request.Access(cat, plan), at(library), Answer.Access(Some(Level.View)), at(library),
        "Cat has no access to the plan"))

  /** The handling: the time, the library, the one the request leads to kept when it differs, the answer.
    * HandleContract is proven of it, on the store's and the clock's models.
    */
  def handleRequest(r: Term[Request]): Flow[Answer] =
    for
      t    <- Flow.now
      lib  <- store.load
      next = afterRequest(lib, t, r)
      _    <- Flow.whenA(next =!= lib)(store.save(next))
    yield answerTo(lib, t, r)
