package sharing.store

import frflow.*
import sharing.domain.*

/** Where the library is kept, as proven code sees it: it gives the library it holds, and holds a new one. */
trait LibraryStore[F[_], T[_]] derives BoundaryOps:
  def load: F[T[Library]]
  def save(library: T[Library]): F[Unit]

/** The store as the proofs see it: one library, given back as it was last saved. */
final class Kept[F[_]](state: Model[F, Library]) extends LibraryStore[F, Term]:
  def load: F[Term[Library]] = state.get
  def save(library: Term[Library]): F[Unit] = state.set(library)

/** The store's boundary, its model, and what it is decided to do. */
object LibraryStore:
  val store = Boundary.failing[LibraryStore, Failure](
    "where the service keeps the library: in memory, or in a SQLite file; it may be down", Failure.StoreUnavailable)

  val libraryModel = store.model("the library the store holds")(Kept(_))

  val libraryKept = Node.assumption("The store gives the library it holds, and after a save holds the library saved, " +
      "in place of the one it held; any call may fail because the store is down, and then changes nothing.")(
    store.behavesAs(libraryModel))

  val oneTransactionAtATime = Node.assumption("Each request, each run of housekeeping and each notice's removal from " +
      "the outbox is one transaction on the store: no step of another comes between two of its steps.")(
    store.atomic)
