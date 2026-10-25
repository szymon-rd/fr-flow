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
