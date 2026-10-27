package sharing.audit

import frflow.*
import sharing.*
import sharing.audit.Audit.*
import sharing.domain.*

/** Audit's claims: what its code is proven to do, each refining a branch or the purpose. */
object AuditClaims:
  val recordContract = Node.claim("Recording a change at a moment adds one entry at the end of the log: numbered by " +
      "its place in it, with the moment and the change. Nothing else changes, and no entry is taken away.")(
    forall((lib: Term[Library], t: Term[BigInt], c: Term[Change]) =>
      record(lib, t, c) === lib.updated(_.log, lib.log :+ make[Entry](lib.log.length, t, c))))
    .refines(auditTrail, sharing.noticesFollowChanges,
      sharing.time.Deadlines.invitationsLapseOnTime, sharing.time.Deadlines.trashPurgedOnTime,
      sharing.time.Deadlines.requestsAnsweredOnTime)

  val forgetContract = Node.claim("Housekeeping forgets, at a moment, the change of each log entry made more than a " +
      "year before, unless the entry is the making of a share the library holds or of a change a notice waiting in " +
      "the outbox tells of: the entry stays in its place, with its number and time, and its change is forgotten. " +
      "Nothing else changes.")(
    forall((lib: Term[Library], t: Term[BigInt]) => forget(lib, t) === lib.updated(_.log, lib.log.map(e =>
      when(e.at <= t - year && !explains(lib, e))(e.updated(_.change, Change.Forgotten)).otherwise(e)))))
    .refines(auditTrail)
