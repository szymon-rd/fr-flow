package sharing.store

import frflow.*
import sharing.domain.*

/** Where the library is kept, as proven code sees it: its two operations, the library it holds and a new one held, and
  * their model, one library given back as it was last saved; and what the world outside does with it.
  */
object LibraryStore:
  val load = Definition[Flow[Library]]("the library the store holds")
  val save = Definition[Library => Flow[Unit]]("a library held by the store in place of the one it held")

  object libraryModel extends StateModel.failing[Library, Failure](
      "where the service keeps the library: in memory, or in a SQLite file; it may be down", Failure.StoreUnavailable):
    load.means(state.get)
    save.means(library => state.set(library))

  val libraryKept = Node.assumption("Nothing but the service's programs changes the library the store holds.")(
    libraryModel.onlyCodeChanges)

  val libraryStarts = Node.assumption("The service starts with an empty library.")(
    libraryModel.initially(lib => lib === (Library(Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil): Term[Library])))

  val oneTransactionAtATime = Node.assumption("No step of another transaction on the store comes between two steps " +
      "of a request, of a run of housekeeping, or of a notice's removal from the outbox.")(
    libraryModel.atomic)
