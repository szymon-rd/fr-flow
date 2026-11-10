package frflow.dsl.lifted

/** The reader's tests' domain: bookings of rooms, as rooms' are, and shapes, an enum. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives FrSpec:
  /** A method the compiler inlines where it is called: lifted code reads its body. */
  inline def covers(t: BigInt): Boolean = start <= t && t < end

final case class RoomBookings(room: String, bookings: List[Booking]) derives FrSpec

enum Shape derives FrSpec:
  case Circle(radius: BigInt)
  case Rect(width: BigInt, height: BigInt)
  case Empty
