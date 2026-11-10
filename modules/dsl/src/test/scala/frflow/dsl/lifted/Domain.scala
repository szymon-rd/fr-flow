package frflow.dsl.lifted

/** The reader's tests' domain: bookings of rooms, as rooms' are, and shapes, an enum. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives FrSpec:
  /** A method the compiler inlines where it is called: lifted code reads its body. */
  inline def covers(t: BigInt): Boolean = start <= t && t < end
  inline def length: BigInt = end - start
  /** Ordinary methods: lifted code reads their bodies when the compiler kept them (`-Yretain-trees`). */
  def span: BigInt = end - start
  def lasts(least: BigInt): Boolean = least <= span
  def endsBy(other: Booking): Boolean = end <= other.start

final case class RoomBookings(room: String, bookings: List[Booking]) derives FrSpec

enum Shape derives FrSpec:
  case Circle(radius: BigInt)
  case Rect(width: BigInt, height: BigInt)
  case Empty

/** A type with no `FrSpec`: lifted code cannot hold a value of it. */
final case class Unspecified(x: BigInt)

/** Ordinary functions of an object, one calling another, and one calling itself. */
object Rules:
  def apart(a: Booking, b: Booking): Boolean = a.room != b.room || a.endsBy(b) || b.endsBy(a)
  def free(held: List[Booking], request: Booking): Boolean = held.forall(b => apart(b, request))
  def countdown(n: BigInt): BigInt = if n < BigInt(1) then n else countdown(n - BigInt(1))
