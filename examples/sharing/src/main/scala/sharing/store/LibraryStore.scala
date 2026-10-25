package sharing.store

import frflow.*
import sharing.domain.*

/** Where the library is kept, as proven code sees it: it gives the library it holds, and holds a new one. */
trait LibraryStore:
  def load: Flow[Library]
  def save(library: Term[Library]): Flow[Unit]

/** The store as the proofs see it: one library, given back as it was last saved. */
object LibraryModel extends LibraryStore, StateModel[Library]:
  def load = state.get
  def save(library: Term[Library]) = state.set(library)

/** The store's boundary, and what it is decided to do. */
object LibraryStore:
  val store = Boundary.failing[LibraryStore]("store", "where the service keeps the library: in memory, or in a SQLite file; it may be down")(
    Failure.StoreUnavailable: Term[Failure])

  val libraryKept = Node.assumption(store)(LibraryModel)("LibraryKept",
    "The store gives the library it holds, and after a save holds the library saved, in place of the one it held; any call may fail because the store is down, and then changes nothing.",
    why = "Proven flows are proven from this model, not from the store's code, for every pattern of failures. MemoryLibraryStore, the service's own store, is tested against it; SQLite, an outside system, is checked against it: SqlLibraryStore keeps each list's order in its rows and replaces every row in one transaction, so a save that fails changes nothing (Q16). The log and the outbox are saved with the library: a change, its entry and its notices in one transaction, and the log is never cut (Q15).",
    idea = "Who can see and change what")
    .implementedBy(l => MemoryLibraryStore(l), _.library)
    .checkedAgainst(l => SqlLibraryStore.holding(l), _.library)

  /** What the store gives requests at once: transactions. Decided, not proven: Lean reads a transaction as one step. */
  val transactions = Node.design("Transactions",
    "Each request, each run of housekeeping and each notice's removal from the outbox is one transaction on the store (atomically): no step of another comes between two of its steps, so requests at once leave the store as one after the other leaves it, in the order they take the store; once begun, a transaction runs to its end. Reading the clock is not part of the store's transaction.",
    why = "Q18, Q19, Q21: the service is one process with SQLite as its one store, so FrFlow's atomically, a lock on the store held for the transaction, gives what Q18 asked of compare-and-set on a version (a transaction run again on a conflict); with more than one process the store would have to give it. The proofs read each transaction as one step of the run (HandleContract, HousekeepingJob, DeliveryJob, the run's events), and are proofs of the serial orders; that the runtime keeps to them is this decision, tested with many clients at once (SharingSuite).",
    idea = "Concurrency"
  )("src/main/scala/sharing/store/MemoryLibraryStore.scala")
    .under(sharing.http.SharingHttp.handleContract, sharing.housekeeping.Housekeeping.jobContract, sharing.notifications.Notifications.deliveryJob)
