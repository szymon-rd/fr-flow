package sharing.audit

import frflow.*
import sharing.*
import sharing.domain.*

/** The log: every change the service makes, recorded with the request that made it (who asked, what) and when, in the
  * same save as the change. A function of the library and of the moment.
  */
object Audit:
  val record = Definition[(Library, BigInt, Change) => Library]("the library with a change recorded in its log")
  val forget = Definition[(Library, BigInt) => Library]("the library with the changes of its old log entries forgotten")

  /** A share for good, of what with a person, at a level. */
  private def forGood(s: Term[Share], what: Term[Target], p: Term[PersonId]): Term[Boolean] =
    s.what === what && s.withWhom === make[Grantee.Person](p) && !s.until.isDefined

  /** Whether a request made a share: the share asked for, an accepted invitation, an approved access request, or a
    * document handed on (the new owner's share).
    */
  val madeBy = define { (r: Term[Request], s: Term[Share]) =>
    r.on[Request.Access]((_, _) => False)
      .on[Request.Share]((_, what, withWhom, level, until) => s === make[Share](what, withWhom, level, until))
      .on[Request.Unshare]((_, _, _) => False)
      .on[Request.Move]((_, _, _) => False)
      .on[Request.Invite]((_, _, _, _) => False)
      .on[Request.Accept]((p, what) => forGood(s, what, p))
      .on[Request.Withdraw]((_, _, _) => False)
      .on[Request.Trash]((_, _) => False)
      .on[Request.Restore]((_, _) => False)
      .on[Request.Ask]((_, _, _) => False)
      .on[Request.Approve]((_, p, w) => forGood(s, w, p))
      .on[Request.Decline]((_, _, _) => False)
      .on[Request.Transfer]((_, d, to) =>
        s === make[Share](make[Target.Doc](d), make[Grantee.Person](to), Level.Edit: Term[Level], none[BigInt])) }

  /** Whether a log entry is of the request that made a share. */
  val makes = define { (e: Term[Entry], s: Term[Share]) =>
    e.change.on[Change.Made](r => madeBy(r, s)).on[Change.Housekept.type](False).on[Change.Forgotten.type](False) }

  val recordCode = define { (lib: Term[Library], t: Term[BigInt], c: Term[Change]) =>
    lib.updated(_.log, lib.log :+ make[Entry](lib.log.length, t, c)) }

  /** A year, in seconds: how long the log keeps what an entry tells. */
  val year: BigInt = 365 * BigInt(86400)

  /** Whether an entry still explains something: the making of a share the library holds, or the change a notice
    * waiting in the outbox tells of.
    */
  val explains = define { (lib: Term[Library], e: Term[Entry]) =>
    lib.shares.exists(s => makes(e, s)) || lib.outbox.exists(n => n.about === make[Subject.Logged](e)) }

  val forgetCode = define { (lib: Term[Library], t: Term[BigInt]) =>
    lib.updated(_.log, lib.log.map(e =>
      when(e.at <= t - year && !explains(lib, e))(e.updated(_.change, Change.Forgotten)).otherwise(e))) }
