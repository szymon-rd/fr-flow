package frflow.eval.flow

import frflow.*

/** Operations on a state of the tests: a shelf of numbers, which may be down, and FrFlow's clock; their models, and
  * their plain Scala (`PlainShelf`, `Wall`).
  */
object Shelf:
  val items = Definition[Program[List[BigInt]]]("the numbers on the shelf, oldest first")
  val put = Definition[BigInt => Program[Unit]]("a number put on the shelf")

  object kept extends StateModel.failing[List[BigInt], Trouble]("the numbers on the shelf, oldest first",
      Trouble.Down):
    items.means(state.get)
    put.means(n => state.update(held => held :+ n))

  /** The shelf and the clock as their models: what the recorded programs are run on; their plain Scala. */
  val knowledge: FrModel = FrModel("Shelves")(
    Node.assumption("Nothing but the programs change the shelf.")(kept.onlyCodeChanges),
    Node.assumption("The clock moves only when a program sleeps.")(Clock.clockModel.onlyCodeChanges))
    .implementTested(items, put)(start = PlainShelf.holding, observe = _.held)(s => (s.items, s.put))
    .implementTested(Clock.now, Clock.sleep)(start = Wall.at, observe = _.time)(c => (c.now, c.sleep))

  /** The shelf's operations as a program calls them, over its effect. */
  final class On[F[_]](using f: Flow[F]):
    def items: F[Term[List[BigInt]]] = f.step(Shelf.items)
    def put(n: Term[BigInt]): F[Unit] = f.run(Shelf.put(n))

  /** The clock's operations as a program calls them. */
  final class Ticking[F[_]](using f: Flow[F]):
    def now: F[Term[BigInt]] = f.step(Clock.now)
    def sleep(seconds: Term[BigInt]): F[Unit] = f.run(Clock.sleep(seconds))

  /** The two, as a program's steps on `f`. */
  def on[F[_]](f: Flow[F]): (On[F], Ticking[F]) = (On[F](using f), Ticking[F](using f))
