package crm

import java.util.concurrent.{Executors, ScheduledExecutorService, TimeUnit}

/** One run of the expiry job at `now` (seconds): ExpireJob's code on the stored records, shares and
  * expiries, checked against ExpireJob; the rows of each record it changed are stored through
  * StoreEdits. ExpiryJobWiring governs this file.
  */
def expireOnce(db: Db, now: BigInt): CrmStore = db.synchronized {
  val s = db.load()
  val t = knowledge.service(expireJob)()(s, now)
  val store = knowledge.service(storeEdits)(database.bind(db))
  ((s.shares diff t.shares).map(_.record) ++ (s.expiries diff t.expiries).map(_.record)).distinct.foreach(id => store(id, t))
  t
}

/** The job, every minute. */
def startExpiryJob(db: Db): ScheduledExecutorService =
  val ex = Executors.newSingleThreadScheduledExecutor()
  ex.scheduleAtFixedRate(() => expireOnce(db, BigInt(System.currentTimeMillis / 1000)), 0, 60, TimeUnit.SECONDS)
  ex
