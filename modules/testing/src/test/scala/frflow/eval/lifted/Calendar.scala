package frflow.eval.lifted

import frflow.*

/** Rooms' calendar, its decision written in plain Scala and read by FrFlow (`lifted`). What rooms tests of its
  * calendar's plain Scala on generated cases (`grantWhenNoOverlap`), Lean proves here of the Scala itself; the
  * domain's types state their contracts in Scala (`FrSpec`).
  */
object Calendar:
  /** What the booking form sends: it ends after it starts. */
  final case class Booking(room: String, start: BigInt, end: BigInt)

  object Booking:
    given FrSpec[Booking] = FrSpec.derived[Booking].where(b => b.start < b.end)

  /** A room's bookings, as the table gives them. */
  final case class RoomBookings(room: String, bookings: List[Booking]) derives FrSpec

  /** Two bookings do not overlap: they are in different rooms, or one ends by the time the other starts. */
  val noOverlap = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end <= b.start || b.end <= a.start }

  /** The calendar's code: a request is granted when it overlaps no booking held. */
  val grantedCode = lifted { (held: RoomBookings, request: Booking) =>
    held.bookings.forall(b => noOverlap(b, request)) }

  val granted =
    Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

  /** A booking covers the moments from its start up to its end. */
  val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

  /** No moment is covered by both bookings: over every moment, which plain Scala cannot say. */
  val shareNoMoment = define { (a: Term[Booking], b: Term[Booking]) =>
    forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

  /** Two bookings are apart when they are in different rooms or share no moment. */
  val apart = define { (a: Term[Booking], b: Term[Booking]) => a.room =!= b.room || shareNoMoment(a, b) }

  /** A room is free for a request when each of the bookings is apart from it. */
  val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
    bookings.forall(b => apart(b, request)) }

  val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(contractOf[Booking])

  val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === free(held.bookings, request)))
    .assuming(bookingsEndAfterStart)

  val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
    .refines(grantWhenFree)
    .assuming(bookingsEndAfterStart)

  val model: FrModel = FrModel("Calendar")(grantWhenFree, grantWhenNoOverlap, bookingsEndAfterStart)
    .implementProven(granted)(grantedCode)
