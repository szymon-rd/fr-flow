package crm

import frflow.*

// ============================================================================
// Expiring shares: a job clears the shares whose time has come
// ============================================================================

val sharesExpire = Node.claim("A run of the expiry job changes a store only by ending the shares whose time has " +
    "come.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) =>
    val left = expire(s, now)
    sameRecords(s, left) &&
      onlyLiveShares(s, now, left) &&
      onlyLiveTimes(s, now, left)))
  .refines(sharesMirrorGrants, recordsKept)
  .assuming(keyedTables)

val expiryKeepsRecords = Node.claim("A run of the expiry job keeps the records as they are.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) => sameRecords(s, expire(s, now))))
  .refines(sharesExpire)
  .assuming(keyedTables)

val expiryKeepsLiveShares = Node.claim("A run of the expiry job keeps exactly the shares that have not ended.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) => onlyLiveShares(s, now, expire(s, now))))
  .refines(sharesExpire)
  .assuming(keyedTables)

val expiryKeepsLiveTimes = Node.claim("A run of the expiry job keeps exactly the times of the shares that have not " +
    "ended.")(
  forall((s: Term[CrmStore], now: Term[BigInt]) => onlyLiveTimes(s, now, expire(s, now))))
  .refines(sharesExpire)
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

/** What the database holds after a run of the expiry job at `now`. */
private def afterJob(now: Term[BigInt]): Term[Tables] = databaseModel.in(runExpiry(now).after)

val jobStoresExpired = Node.claim("A run of the expiry job leaves the database holding, about each record, what " +
    "expire gives of what it held.")(
  forall((now: Term[BigInt]) => sameRows(afterJob(now).store, expire(held, now))))
  .assuming(runsOneAtATime, keyedTables)

val jobLogsRun = Node.claim("A run of the expiry job is appended to the event log.")(
  forall((now: Term[BigInt]) => afterJob(now).events === history :+ make[Event.Expired](now)))
  .assuming(runsOneAtATime, keyedTables)

val jobReturnsExpired = Node.claim("A run of the expiry job returns what expire gives of what the database held.")(
  forall((now: Term[BigInt]) => runExpiry(now).result === expire(held, now)))
  .assuming(runsOneAtATime, keyedTables)

val expiryJobWiring = Node.design("The expiry job runs its proven program on SQLite.")(
  "src/main/scala/crm/Job.scala")
  .refines(jobStoresExpired, jobLogsRun, jobReturnsExpired)

val expirySchedule = Node.design("The expiry job runs every minute.")(
  "src/main/scala/crm/Job.scala")
  .refines(jobStoresExpired)

val databaseLock = Node.design("Every program on the database holds the database's lock for its whole run.")(
  "src/main/scala/crm/WriteSide.scala", "src/main/scala/crm/Job.scala")
  .refines(saveStores, jobStoresExpired)
