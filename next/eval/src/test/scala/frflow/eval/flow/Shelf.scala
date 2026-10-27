package frflow.eval.flow

import frflow.*

/** A boundary of the tests: a shelf of numbers, which may be down. */
trait Shelf[F[_], T[_]] derives BoundaryOps:
  def items: F[T[List[BigInt]]]
  def put(n: T[BigInt]): F[Unit]

object Shelf:
  val shelf: Boundary[Shelf] = Boundary.failing[Shelf, Trouble]("a shelf of numbers, which may be down", Trouble.Down)
  val clock: Boundary[Clock] = Boundary[Clock]("the time, in seconds")
  val kept = shelf.model("the numbers on the shelf, oldest first")(Kept(_))
  val ticks = clock.model("the time now, in seconds")(Ticks(_))

  /** The shelf and the clock as their models: what the recorded programs are run on. */
  val knowledge: FrModel = FrModel("Shelves")(
    Node.assumption("The shelf keeps the numbers put on it.")(shelf.behavesAs(kept)),
    Node.assumption("The clock moves only when a program sleeps.")(clock.behavesAs(ticks)))
