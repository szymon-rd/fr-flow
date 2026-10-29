package rooms

import cats.effect.IO
import java.sql.Connection
import scala.util.Using

/** The bookings in SQLite, a row each, read back in the order they were added: the table's operations' plain Scala,
  * tested against `storedBookings` (`Knowledge.scala`). One connection, its calls one at a time.
  */
final class BookingsTable private (conn: Connection):
  def inRoom(room: String): IO[RoomBookings] =
    IO.blocking(synchronized(RoomBookings(room, read("where room = ?", List(room)))))
  def add(booking: Booking): IO[Unit] = IO.blocking(synchronized(insert(booking)))
  /** Every booking held, oldest first. */
  def bookings: IO[List[Booking]] = IO.blocking(synchronized(read("", Nil)))

  /** Each statement and its rows closed once read. */
  private def insert(b: Booking): Unit = Using.resource(conn.prepareStatement(
    "insert into bookings (room, starts, ends) values (?, ?, ?)")) { row =>
    List(b.room, b.start.toString, b.end.toString).zipWithIndex.foreach((v, i) => row.setString(i + 1, v))
    val _ = row.executeUpdate()
  }

  private def read(where: String, args: List[String]): List[Booking] = Using.resource(conn.prepareStatement(
    s"select room, starts, ends from bookings $where order by id")) { query =>
    args.zipWithIndex.foreach((v, i) => query.setString(i + 1, v))
    Using.resource(query.executeQuery())(rows => Iterator.continually(rows).takeWhile(_.next())
      .map(r => Booking(r.getString(1), BigInt(r.getString(2)), BigInt(r.getString(3)))).toList)
  }

object BookingsTable:
  /** A table in a file, or `:memory:`: through SQLite's driver itself, not `DriverManager`, which finds drivers by
    * the calling thread's class loader.
    */
  def open(path: String): IO[BookingsTable] = IO.blocking {
    val conn = org.sqlite.JDBC().connect(s"jdbc:sqlite:$path", java.util.Properties())
    val _ = Using.resource(conn.createStatement())(_.executeUpdate("create table if not exists bookings " +
      "(id integer primary key, room text not null, starts text not null, ends text not null)"))
    BookingsTable(conn)
  }

  /** An in-memory table holding the given bookings, in order: what the model test starts from. */
  def holding(bookings: List[Booking]): IO[BookingsTable] =
    open(":memory:").flatTap(t => IO.blocking(t.synchronized(bookings.foreach(t.insert))))
