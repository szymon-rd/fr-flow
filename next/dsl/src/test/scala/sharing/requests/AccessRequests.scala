package sharing.requests

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.service.Sharing.sharesWithout
import sharing.time.Lifetimes.{isPending, reminderDue}

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

  val askCode = define {
    (lib: Term[Library], t: Term[BigInt], p: Term[PersonId], w: Term[Target], level: Term[Level]) =>
      when(holds(lib, w))(lib.updated(_.requests,
        make[AccessRequest](p, w, level, t, False) :: requestsWithout(lib.requests, p, w))).otherwise(lib) }

  /** The library with the request approved: the share asked for, in place of any, and the request gone. */
  val granted = define { (lib: Term[Library], r: Term[AccessRequest]) =>
    val person = make[Grantee.Person](r.person)
    lib.updated(_.shares,
      make[Share](r.what, person, r.level, none[BigInt]) :: sharesWithout(lib.shares, r.what, person))
      .updated(_.requests, requestsWithout(lib.requests, r.person, r.what)) }

  val approveCode = define {
    (lib: Term[Library], t: Term[BigInt], by: Term[PersonId], p: Term[PersonId], w: Term[Target]) =>
      lib.requests.find(r => r.person === p && r.what === w && isPending(r, t)).fold(lib)(r =>
        when(mayEdit(lib, t, by, w) && !ownedBy(lib, w, make[Grantee.Person](p)))(granted(lib, r)).otherwise(lib)) }

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
    lib.requests.filter(r => !isPending(r, t)).map(r => make[Notice](r.person, make[Subject.Lapsed](r))) ++
      lib.requests.filter(r => isPending(r, t) && reminderDue(r, t) && !r.reminded).flatMap(r =>
        lib.documents.filter(doc => isFor(r.what, doc))
          .map(doc => make[Notice](doc.owner, make[Subject.Reminder](r)))) }

  val chaseCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.requests, lib.requests.filter(r => isPending(r, t)).map(r => chased(r, t)))
      .updated(_.outbox, lib.outbox ++ chaseNotices(lib, t)) }
