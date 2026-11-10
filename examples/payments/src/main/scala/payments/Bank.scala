package payments

import cats.effect.{IO, Ref}
import frflow.*

/** The bank's books in memory, read and written whole: the books' two operations' plain Scala, tested against
  * `books`.
  */
final class Bank private (held: Ref[IO, Ledger]):
  def load: IO[Ledger] = held.get
  def save(l: Ledger): IO[Unit] = held.set(l)

/** What the system is made of: the books it keeps, and paying. */
object Bank:
  /** The books as they are kept. */
  val load = Definition[Flow[Ledger]]("the books as they are kept")

  /** A ledger written to the books, in place of the one kept. */
  val save = Definition[Ledger => Flow[Unit]]("a ledger written to the books")

  /** The books: every account with its balance and the payments made. */
  object books extends StateModel[Ledger]("the books: every account with its balance, and the payments made"):
    load.means(state.get)
    save.means(l => state.set(l))

  val nothingElseWrites = Node.assumption("Nothing but paying changes the books.")(books.onlyCodeChanges)

  val oneAtATime = Node.assumption("Payments are handled one at a time.")(books.atomic)

  val startsDistinct = Node.assumption("The books start with no two accounts sharing an id.")(
    books.initially(l => Ledger.distinctIds(l)))

  /** Paying a payment: whether it was made. */
  val pay = Definition[Payment => Flow[Boolean]]("paying a payment: whether it was made")

  /** The program `pay` is: the books read, and the payment applied and written back when it is payable, in one
    * transaction. Lazy: it is code, attached by the model, not a node.
    */
  lazy val paying = program { (p: Term[Payment]) =>
    (for
      l  <- load
      ok  = Ledger.payable(l, p)
      _  <- Flow.when(ok)(save(Ledger.applied(l, p)))
    yield ok).atomically }

  /** Books holding `l`: what the model test starts from. */
  def holding(l: Ledger): IO[Bank] = Ref.of[IO, Ledger](l).map(Bank(_))

  /** `pay` is the program above, proven; `load` and `save` are the in-memory books' Scala, tested against `books`. */
  def implemented(model: FrModel): FrModel =
    model.implementProven(pay)(paying)
      .implementTested(load, save)(start = holding, observe = _.load)(t => (t.load, t.save))
