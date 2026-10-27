package crm

import examples.Folds.*
import frflow.*

// ============================================================================
// Expiring shares: a job clears the shares whose time has come
// ============================================================================

val sharesExpire = Node.claim("A run of the expiry job at a time removes exactly the shares given until then or " +
    "earlier, with their times, and keeps every record and every other share's time.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) => endsDueAt(s, now, expire(s, now))))
  .refines(storeMirrorsRequests, recordsKept)

/** A run: the shares that have not ended, and the expiries of those. */
val expireCode = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  make[CrmStore](s.records, s.shares.filter(sh => !ended(sh, s, now)),
    s.expiries.filter(e => !ended(make[Share](e.record, e.to), s, now))) }

// ============================================================================
// The job on the database: a program, proven from the database's model
// ============================================================================

/** The ids of the records a store holds anything about: its records, their shares and their expiries. */
val idsIn = define { (s: Term[CrmStore]) =>
  s.records.mapped(r => r.id) ++ s.shares.mapped(sh => sh.record) ++ s.expiries.mapped(e => e.record) }

/** The records whose rows differ between two stores: what storing the second over the first must store. */
val changedIds = define { (s: Term[CrmStore], t: Term[CrmStore]) =>
  (idsIn(s) ++ idsIn(t)).filter(id => aboutRecord(s, id) =!= aboutRecord(t, id)) }

/** Whether two stores hold the same rows about every record, in the same order for each. */
val sameRows = define { (a: Term[CrmStore], b: Term[CrmStore]) =>
  (idsIn(a) ++ idsIn(b)).forall(id => aboutRecord(a, id) === aboutRecord(b, id)) }

/** One run of the expiry job at `now`: what the database holds, `expire` on it, the rows of each record whose rows it
  * changed stored, and the run logged.
  */
final class ExpireOnce[F[_]](db: Database[F, Term])(using f: Flow[F]):
  def run(now: Term[BigInt]): F[Term[CrmStore]] = f.flatMap(db.load) { s =>
    val t = expire(s, now)
    f.flatMap(f.each(changedIds(s, t))(id => db.storeAbout(id, t)))(_ =>
      f.as(db.logEvent(make[Event.Expired](now)), t)) }

val expireOnce = program { (now: Term[BigInt]) => ExpireOnce(db.recording).run(now) }

val runsOneAtATime = Node.assumption("Runs on the database never interleave: the expiry job holds the database's " +
    "lock during a run, and the write side saves one write at a time.")(
  databaseModel.changedOneRunAtATime)

val expiryJob = Node.claim("A run of the expiry job at a time leaves the database holding, about each record, what " +
    "sharesExpire's run on what it held gives, logs the run at the end of the event log, and returns that store.")(
  forall((now: Term[BigInt], before: Term[World]) =>
    runExpiry(now).from(before) { (result, after) =>
      sameRows(databaseModel.in(after).store, expire(databaseModel.in(before).store, now)) &&
        databaseModel.in(after).events === databaseModel.in(before).events :+ make[Event.Expired](now) &&
        result === expire(databaseModel.in(before).store, now) }))
  .assuming(tablesModel, runsOneAtATime)

val expiryJobWiring = Node.design("The expiry job runs every minute, holding the database's lock during a run so no " +
    "write interleaves with it; its code is the program expiryJob is proven of, run on SQLite.")(
  "src/main/scala/crm/Job.scala")
  .refines(expiryJob)
