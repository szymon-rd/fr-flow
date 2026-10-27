package sharing.time

import frflow.*

/** FrFlow's clock as the service's programs see it: its operations derived here (the DSL's own module cannot expand
  * its macro), its model a count of seconds only sleeps move.
  */
object ClockKept:
  given BoundaryOps[Clock] = BoundaryOps.derived

  val clock: Boundary[Clock] = Boundary[Clock]("the server's clock, in seconds")

  /** The clock as the proofs see it: the time now, moved on by a sleep. */
  final class Ticks[F[_]: Flow](state: Model[F, BigInt]) extends Clock[F, Term]:
    def now: F[Term[BigInt]] = state.get
    def sleep(seconds: Term[BigInt]): F[Unit] = state.get.flatMap(t => state.set(t + seconds))

  val clockModel = clock.model("the time now, in seconds")(Ticks(_))

  val clockKept = Node.assumption("The clock gives the time now, in seconds; a sleep moves it on by the time asked.")(
    clock.behavesAs(clockModel))

  val clockAlone = Node.assumption("Nothing but a program's own sleeps moves the clock while it runs.")(
    clockModel.changedOneRunAtATime)
