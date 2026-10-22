package crm

import java.util.concurrent.{Executors, ScheduledExecutorService, TimeUnit}

/** One run of the expiry job at `now` (seconds): SharesExpire's code on the stored records, shares and
  * expiries, checked against SharesExpire; the rows of each record it changed are stored through
  * StoreEdits, and the run is logged in the event log. ExpiryJobWiring governs this file.
  */
def expireOnce(db: Db, now: BigInt): CrmStore = db.synchronized {
  val s = db.load()
  val t = knowledge.service(sharesExpire)()(s, now)
  val storeAbout = knowledge.service(storeEdits)(database.bind(db))
  ((s.shares diff t.shares).map(_.record) ++ (s.expiries diff t.expiries).map(_.record)).distinct.foreach(id => storeAbout(id, t))
  db.logEvent(Event.Expired(now))
  t
}

/** The job, every minute. */
def startExpiryJob(db: Db): ScheduledExecutorService =
  val ex = Executors.newSingleThreadScheduledExecutor()
  ex.scheduleAtFixedRate(() => expireOnce(db, BigInt(System.currentTimeMillis / 1000)), 0, 60, TimeUnit.SECONDS)
  ex
