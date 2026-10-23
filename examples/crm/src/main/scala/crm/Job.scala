package crm

import cats.effect.{IO, SyncIO}
import frflow.*
import java.util.concurrent.{Executors, ScheduledExecutorService, TimeUnit}

/** One run of the expiry job at `now` (seconds): what the database holds, SharesExpire's operation on it, the rows
  * of each record whose rows it changed stored, and the run logged. ExpiryJob is proven of it; ExpiryJobWiring
  * governs this file.
  */
def expireOnce(now: Term[BigInt]): Flow[CrmStore] =
  for
    s <- db.load
    t  = expire(s, now)
    _ <- changedIds(s, t).traverse_(id => db.storeAbout(id, t))
    _ <- db.logEvent(Event[Event.Expired](now))
  yield t

/** The job on a database, now, with the database to itself: run in `SyncIO`, on this thread, which holds the
  * database's lock (`IO` would run the steps on other threads, which would wait for the lock this one holds).
  */
def runExpiryJob(d: Db, now: BigInt): CrmStore = d.synchronized {
  knowledge.run[SyncIO](expiryJob)(db.bind(SqliteDatabase(d)))(now).unsafeRunSync()
}

/** A run in `IO`, for a caller that ensures no write interleaves with it. */
def expiryJobIO(d: Db): BigInt => IO[CrmStore] = knowledge.run[IO](expiryJob)(db.bind(SqliteDatabase(d)))

/** The job, every minute. */
def startExpiryJob(d: Db): ScheduledExecutorService =
  val ex = Executors.newSingleThreadScheduledExecutor()
  ex.scheduleAtFixedRate(() => runExpiryJob(d, BigInt(System.currentTimeMillis / 1000)), 0, 60, TimeUnit.SECONDS)
  ex
