package sharing.store

import frflow.*
import sharing.features.HousekeepingClaims
import sharing.notifications.NotificationsClaims

/** What the store gives requests at once, in an object of its own: it refines the programs' claims, which rest on the
  * store's model, so it is set once they are.
  */
object Transactions:
  /** What the store gives requests at once: transactions. Decided, not proven: Lean reads a transaction as one step. */
  val transactions = Node.design("Each request, each run of housekeeping and each notice's removal from the outbox " +
      "runs to its end as one transaction on the store, which reading the clock is not part of.")(
    "src/main/scala/sharing/store/MemoryLibraryStore.scala")
    .refines(sharing.features.SharingHttp.handleContract, HousekeepingClaims.housekeepingJob,
      NotificationsClaims.deliveryJob)
