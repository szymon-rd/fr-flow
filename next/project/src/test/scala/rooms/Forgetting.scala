package rooms

import cats.effect.{IO, Ref}
import frflow.*

/** Rooms with no `neverOverlap` and so no assumption that only the code writes the table, its claims about booking's
  * runs resting on the table being atomic alone, and the table's Scala a stand-in that forgets to add (review 11b,
  * B3): the claims rest on that Scala, tested against the model, all the same.
  */
object Forgetting:
  /** The bookings in memory, a booking added never kept. */
  final class Table(held: Ref[IO, List[Booking]]):
    def inRoom(room: String): IO[RoomBookings] = held.get.map(bs => RoomBookings(room, bs.filter(_.room == room)))
    def add(booking: Booking): IO[Unit] = IO(booking).void
    def bookings: IO[List[Booking]] = held.get

  private val dropped = Set("neverOverlap", "nothingElseWrites", "startsEmpty")

  val kb: FrModel = forgetting(rooms.nodes.filterNot(n => dropped(n.head.id.value)))

  /** Rooms as it is, every node kept, its table's Scala the one that forgets to add (review 11b, R2). */
  val everyNode: FrModel = forgetting(rooms.nodes)

  private def forgetting(nodes: List[Node]): FrModel = FrModel("Rooms")(nodes*)
    .copy(generators = rooms.generators)
    .implementProven(book)(bookIfGranted)
    .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
    .implementTested(inRoom, add)(start = (bs: List[Booking]) => Ref[IO].of(bs).map(Table(_)),
      observe = (t: Table) => t.bookings)(t => (t.inRoom, t.add))
