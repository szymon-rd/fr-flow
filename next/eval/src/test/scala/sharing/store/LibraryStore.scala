package sharing.store

import frflow.*
import sharing.domain.*

/** Where the library is kept, as proven code sees it: its two operations, the library it holds and a new one held, and
  * their model, one library given back as it was last saved; and what the world outside does with it.
  */
object LibraryStore:
  val load = Definition[Program[Library]]("the library the store holds")
  val save = Definition[Library => Program[Unit]]("a library held by the store in place of the one it held")

  object libraryModel extends StateModel.failing[Library, Failure](
      "where the service keeps the library: in memory, or in a SQLite file; it may be down", Failure.StoreUnavailable):
    load.means(state.get)
    save.means(library => state.set(library))

  val libraryKept = Node.assumption("Nothing but the service's programs changes the library the store holds.")(
    libraryModel.onlyCodeChanges)

  val oneTransactionAtATime = Node.assumption("Each request, each run of housekeeping and each notice's removal from " +
      "the outbox is one transaction on the store: no step of another comes between two of its steps.")(
    libraryModel.atomic)
