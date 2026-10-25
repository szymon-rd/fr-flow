package sharing.http

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing
import sharing.store.{LibraryModel, LibraryStore}
import sharing.store.LibraryStore.store

/** The service as clients reach it: a request, answered from the library the store keeps, and the store left holding
  * the library the request leads to. `HttpCodec` turns HTTP into requests and answers into HTTP; `Server` serves it.
  */
trait SharingHttp:
  def handle(request: Request): Answer

/** The handling of a request and its contract. */
object SharingHttp:
  import Demo.*

  val handle = Param[Request => Flow[Answer]]("handle", "a request handled on the store: the answer, the store left holding the change")

  /** The library a request leads to: Sharing's change for a change; the same library for a question. */
  val afterRequest = define { (lib: Term[Library], r: Term[Request]) =>
    r.on[Request.Access]((_, _) => lib)
      .on[Request.Share]((by, what, withWhom, level) => Sharing.share(lib, by, what, withWhom, level))
      .on[Request.Unshare]((by, what, withWhom) => Sharing.unshare(lib, by, what, withWhom))
      .on[Request.Move]((by, d, into) => Sharing.move(lib, by, d, into))
  }

  /** Done when the asker may make the change, refused otherwise. */
  private def allowedWhen(c: Term[Boolean]): Term[Answer] = c.fold(Answer.Done: Term[Answer], Answer.Refused: Term[Answer])

  /** The answer to a request: the person's access to the document; for a change, whether the asker may make it. */
  val answerTo = define { (lib: Term[Library], r: Term[Request]) =>
    r.on[Request.Access]((p, d) => Answer[Answer.Access](Sharing.access(lib, p, d)))
      .on[Request.Share]((by, what, _, _) => allowedWhen(mayEdit(lib, by, what)))
      .on[Request.Unshare]((by, what, _) => allowedWhen(mayEdit(lib, by, what)))
      .on[Request.Move]((by, d, into) => allowedWhen(Sharing.mayMove(lib, by, d, into)))
  }

  private val bobViewsPlan = library.copy(shares = Share(Target.Doc(plan), Grantee.Person(bob), Level.View) :: library.shares)

  val handleContract = Node.contract(handle)("HandleContract",
    "A request is answered from the library the store holds, and leaves the store holding the library it leads to: a question is answered with the person's access and changes nothing; a change is made as Sharing makes it, and answered done when the asker may make it and refused otherwise.",
    why = "This is the service as a client sees it, in the store's terms (LibraryKept). What the answers and changes are is Sharing's (its contracts); what this adds is that each request reads the library the last one left and leaves the one it leads to, so a client's next request sees its change.",
    idea = "Who can see and change what"
  )((r, result, before, after) =>
    after(LibraryModel) === afterRequest(before(LibraryModel), r) && result === answerTo(before(LibraryModel), r))
    .under(accessFollowsShares)
    .examples()(
      expect(Request.Access(bob, q3Report), World(LibraryModel -> library), Answer.Access(Some(Level.View)), World(LibraryModel -> library),
        "Bob's team may view the reports folder: Bob can view the Q3 report, and nothing changes"),
      expect(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View), World(LibraryModel -> library), Answer.Done,
        World(LibraryModel -> bobViewsPlan), "Ann shares the plan with Bob: the store holds the new share"),
      expect(Request.Share(bob, Target.Doc(plan), Grantee.Person(bob), Level.Edit), World(LibraryModel -> library), Answer.Refused,
        World(LibraryModel -> library), "Bob may not edit the plan: refused, and the store keeps the library"),
      reject(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View), World(LibraryModel -> library), Answer.Done,
        World(LibraryModel -> library), "a change answered done is kept"),
      reject(Request.Access(cat, plan), World(LibraryModel -> library), Answer.Access(Some(Level.View)), World(LibraryModel -> library),
        "Cat has no access to the plan"))

  /** The handling: load the library, keep the one the request leads to when it differs, answer. HandleContract is proven
    * of it, on the store's model.
    */
  def handleRequest(r: Term[Request]): Flow[Answer] =
    for
      lib <- store.load
      next = afterRequest(lib, r)
      _ <- Flow.whenA(next =!= lib)(store.save(next))
    yield answerTo(lib, r)
