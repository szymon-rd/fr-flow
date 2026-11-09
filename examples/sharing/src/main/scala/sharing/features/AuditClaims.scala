package sharing.features

import frflow.*
import sharing.*
import sharing.domain.*
import sharing.features.Audit.*

/** Audit's claims: what its code is proven to do, each refining a branch or the purpose. */
object AuditClaims:
  val recordContract = Node.claim("Recording a change at a moment adds one entry for it, numbered by its place, at " +
      "the end of the log and changes nothing else.")(
    forall((lib: Term[Library], t: Term[BigInt], c: Term[Change]) =>
      record(lib, t, c) === lib.updated(_.log, lib.log :+ make[Entry](lib.log.length, t, c))))
    .refines(auditTrail, sharing.noticesFollowChanges)

  val forgetContract = Node.claim("Housekeeping forgets the change of each log entry over a year old that explains " +
      "no share held and no waiting notice, keeping the entry in its place.")(
    forall((lib: Term[Library], t: Term[BigInt]) => forget(lib, t) === lib.updated(_.log, lib.log.map(e =>
      when(e.at <= t - year && !explains(lib, e))(e.updated(_.change, Change.Forgotten)).otherwise(e)))))
    .refines(auditTrail)
