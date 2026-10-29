package frflow.eval.flow

import frflow.*

/** Operations on a state of the tests: a shelf of numbers, which may be down, and FrFlow's clock; their models, and
  * their plain Scala (`PlainShelf`, `Wall`).
  */
object Shelf:
  val items = Definition[Flow[List[BigInt]]]("the numbers on the shelf, oldest first")
  val put = Definition[BigInt => Flow[Unit]]("a number put on the shelf")

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

  /** The shelf's and the clock's operations as a program's steps. */
  def held: Flow[List[BigInt]] = Flow.step(items)
  def putting(n: Term[BigInt]): Flow[Unit] = Flow.step(put(n))
  def now: Flow[BigInt] = Flow.step(Clock.now)
  def sleeping(seconds: Term[BigInt]): Flow[Unit] = Flow.step(Clock.sleep(seconds))
