package sharing.store

import frflow.*

/** What the store gives requests at once, in an object of its own: it refines the programs' claims, which rest on the
  * store's model, so it is set once they are.
  */
object Transactions:
  /** What the store gives requests at once: transactions. Decided, not proven: Lean reads a transaction as one step. */
  val transactions = Node.design("Each request, each run of housekeeping and each notice's removal from the outbox " +
      "is one transaction on the store (atomically): requests at once leave the store as one after the other leaves " +
      "it, in the order they take the store; once begun, a transaction runs to its end. Reading the clock is not " +
      "part of the store's transaction.")(
    "src/main/scala/sharing/store/MemoryLibraryStore.scala")
    .refines(sharing.http.SharingHttp.handleContract, sharing.housekeeping.Housekeeping.housekeepingJob,
      sharing.notifications.Notifications.deliveryJob)
