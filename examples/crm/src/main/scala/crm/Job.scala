package crm

import java.util.concurrent.{Executors, ScheduledExecutorService, TimeUnit}

/** One run of the expiry job at `now` (seconds): ExpireJob's code on the stored records and shares,
  * checked against ExpireJob, and stored. ExpiryJobWiring governs this file.
  */
def expireOnce(db: Db, now: BigInt): CrmStore = db.synchronized {
  val t = knowledge.service(expireJob)(expiries.bind(db.expiries()))(db.load(), now)
  db.save(t)
  t
}

/** The job, every minute. */
def startExpiryJob(db: Db): ScheduledExecutorService =
  val ex = Executors.newSingleThreadScheduledExecutor()
  ex.scheduleAtFixedRate(() => expireOnce(db, BigInt(System.currentTimeMillis / 1000)), 0, 60, TimeUnit.SECONDS)
  ex
