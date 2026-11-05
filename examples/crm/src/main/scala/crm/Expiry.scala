package crm

import frflow.*

// ============================================================================
// Expiring shares: a job clears the shares whose time has come
// ============================================================================

val sharesExpire = Node.claim("A run of the expiry job at a time removes exactly the shares given until then or " +
    "earlier, with their times, and keeps every record and every other share's time.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) => endsDueAt(s, now, expire(s, now))))
  .refines(storeMirrorsRequests, recordsKept)
  .assuming(keyedTables)

// ============================================================================
// The job on the database: a program, proven on the database's model
// ============================================================================

/** Whether two stores hold the same rows about every record, in the same order for each. */
val sameRows = define { (a: Term[CrmStore], b: Term[CrmStore]) =>
  (idsIn(a) ++ idsIn(b)).forall(id => aboutRecord(a, id) === aboutRecord(b, id)) }

/** One run of the expiry job at `now`: what the database holds, `expire` on it, the rows of each record stored again
  * if it changed them, and the run logged.
  */
val expireOnce = program { (now: Term[BigInt]) =>
  for
    s <- load
    t  = expire(s, now)
    _ <- Flow.each(idsIn(s) ++ idsIn(t))(id =>
           Flow.ifM[Unit](Flow.pure(aboutRecord(s, id) =!= aboutRecord(t, id)))(storeAbout(id, t), Flow.unit))
    _ <- logEvent(make[Event.Expired](now))
  yield t }

val expiryJob = Node.claim("A run of the expiry job at a time leaves the database holding, about each record, what " +
    "sharesExpire's run on what it held gives, logs the run at the end of the event log, and returns that store.")(
  forall((now: Term[BigInt]) =>
    val (held, left) = (databaseModel.current, databaseModel.in(runExpiry(now).after))
    sameRows(left.store, expire(held.store, now)) && left.events === held.events :+ make[Event.Expired](now) &&
      runExpiry(now).result === expire(held.store, now)))
  .assuming(runsOneAtATime, keyedTables)

val expiryJobWiring = Node.design("The expiry job runs every minute, holding the database's lock during a run so no " +
    "write interleaves with it; its code is the program expiryJob is proven of, run on SQLite.")(
  "src/main/scala/crm/Job.scala")
  .refines(expiryJob)
