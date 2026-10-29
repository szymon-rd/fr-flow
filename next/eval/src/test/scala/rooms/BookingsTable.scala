package rooms

import cats.effect.IO
import java.sql.{Connection, DriverManager, PreparedStatement}

/** The bookings in SQLite, a row each, read back in the order they were added: the table's operations' plain Scala,
  * tested against `storedBookings` (`Knowledge.scala`). One connection, its calls one at a time.
  */
final class BookingsTable private (conn: Connection):
  def inRoom(room: String): IO[RoomBookings] =
    IO.blocking(synchronized(RoomBookings(room, read(selected("where room = ?", List(room))))))
  def add(booking: Booking): IO[Unit] = IO.blocking(synchronized(insert(booking)))
  /** Every booking held, oldest first. */
  def bookings: IO[List[Booking]] = IO.blocking(synchronized(read(selected("", Nil))))

  private def selected(where: String, args: List[String]): PreparedStatement =
    val query = conn.prepareStatement(s"select room, starts, ends from bookings $where order by id")
    args.zipWithIndex.foreach((v, i) => query.setString(i + 1, v))
    query

  private def insert(b: Booking): Unit =
    val row = conn.prepareStatement("insert into bookings (room, starts, ends) values (?, ?, ?)")
    List(b.room, b.start.toString, b.end.toString).zipWithIndex.foreach((v, i) => row.setString(i + 1, v))
    val _ = row.executeUpdate()

  private def read(query: PreparedStatement): List[Booking] =
    val rows = query.executeQuery()
    Iterator.continually(rows).takeWhile(_.next())
      .map(r => Booking(r.getString(1), BigInt(r.getString(2)), BigInt(r.getString(3)))).toList

object BookingsTable:
  /** A table in a file, or `:memory:`. */
  def open(path: String): IO[BookingsTable] = IO.blocking {
    val conn = DriverManager.getConnection(s"jdbc:sqlite:$path")
    val _ = conn.createStatement().executeUpdate("create table if not exists bookings " +
      "(id integer primary key, room text not null, starts text not null, ends text not null)")
    BookingsTable(conn)
  }

  /** An in-memory table holding the given bookings, in order: what the model test starts from. */
  def holding(bookings: List[Booking]): IO[BookingsTable] =
    open(":memory:").flatTap(t => IO.blocking(t.synchronized(bookings.foreach(t.insert))))
