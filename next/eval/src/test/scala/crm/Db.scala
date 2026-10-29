package crm

import java.sql.{Connection, PreparedStatement, ResultSet}
import scala.util.Using

/** The CRM's records, shares, expiries and event log in SQLite: the plain Scala behind `fetch`, `storeRows` and the
  * database model's operations, tested against `recordsByQuery`, `storeEdits` and `databaseModel`. Its tables have
  * one row per key (their keys unique), as `keyedTables` trusts, each read in the order its rows were stored. One
  * connection, its calls one at a time.
  */
final class Db private (conn: Connection, select: Search => (String, List[Any])):
  /** The stored records a search asks for, by SQL. */
  def recordsMatching(q: Search): List[CrmRecord] = synchronized {
    val (where, args) = select(q)
    rows(s"select id, tenant, kind, title from records $where order by seq", args)(record)
  }

  /** What it holds: the records, shares and expiries, each table in the order its rows were stored. */
  def load(): CrmStore = synchronized(CrmStore(rows("select id, tenant, kind, title from records order by seq", Nil)(
    record), rows("select record, tenant from shares order by seq", Nil)(share),
    rows("select record, tenant, until from expiries order by seq", Nil)(expiry)))

  /** Replaces what is stored about record `id` with what `t` holds about it, in one transaction; returns the rows
    * about it, read back in the order stored.
    */
  def storeAbout(id: BigInt, t: CrmStore): CrmStore = synchronized {
    conn.setAutoCommit(false)
    try
      List("records where id", "shares where record", "expiries where record").foreach(table =>
        update(s"delete from $table = ?", List(id.toLong)))
      insert(CrmStore(t.records.filter(_.id == id), t.shares.filter(_.record == id), t.expiries.filter(_.record == id)))
      conn.commit()
    catch
      case e: Exception =>
        conn.rollback()
        throw e
    finally conn.setAutoCommit(true)
    CrmStore(rows("select id, tenant, kind, title from records where id = ? order by seq", List(id.toLong))(record),
      rows("select record, tenant from shares where record = ? order by seq", List(id.toLong))(share),
      rows("select record, tenant, until from expiries where record = ? order by seq", List(id.toLong))(expiry))
  }

  /** Appends an event to the log. */
  def logEvent(e: Event): Unit = synchronized(update("insert into events (event) values (?)", List(Events.text(e))))

  /** The log, in order. */
  def events(): List[Event] = synchronized(rows("select event from events order by seq", Nil)(r =>
    Events.read(r.getString(1))))

  def tables: Tables = Tables(load(), events())
  def close(): Unit = conn.close()

  private def insert(s: CrmStore): Unit =
    s.records.foreach(x => update("insert into records (id, tenant, kind, title) values (?, ?, ?, ?)",
      List(x.id.toLong, x.tenant.value, x.kind.toString, x.title)))
    s.shares.foreach(x => update("insert into shares (record, tenant) values (?, ?)",
      List(x.record.toLong, x.to.value)))
    s.expiries.foreach(x => update("insert into expiries (record, tenant, until) values (?, ?, ?)",
      List(x.record.toLong, x.to.value, x.until.toLong)))

  private def prepared[T](sql: String, args: List[Any])(use: PreparedStatement => T): T =
    Using.resource(conn.prepareStatement(sql)) { st =>
      args.zipWithIndex.foreach((a, i) => st.setObject(i + 1, a))
      use(st)
    }
  private def update(sql: String, args: List[Any]): Unit = prepared(sql, args)(st => { val _ = st.executeUpdate() })
  private def rows[T](sql: String, args: List[Any])(read: ResultSet => T): List[T] = prepared(sql, args)(st =>
    Using.resource(st.executeQuery())(rs => Iterator.continually(rs).takeWhile(_.next()).map(read).toList))

  private def record(r: ResultSet) =
    CrmRecord(BigInt(r.getLong(1)), TenantId(r.getString(2)), Kind.valueOf(r.getString(3)), r.getString(4))
  private def share(r: ResultSet) = Share(BigInt(r.getLong(1)), TenantId(r.getString(2)))
  private def expiry(r: ResultSet) = Expiry(BigInt(r.getLong(1)), TenantId(r.getString(2)), BigInt(r.getLong(3)))

object Db:
  /** The search's SQL: a record by its id, the records of a kind, or every record. */
  val selecting: Search => (String, List[Any]) =
    case Search.ById(id)   => ("where id = ?", List(id.toLong))
    case Search.OfKind(k)  => ("where kind = ?", List(k.toString))
    case Search.Everything => ("", Nil)

  /** An in-memory database holding the tables given, its searches by `select`: through SQLite's driver itself, not
    * `DriverManager`, which finds drivers by the calling thread's class loader.
    */
  def holding(t: Tables, select: Search => (String, List[Any]) = selecting): Db =
    val conn = org.sqlite.JDBC().connect("jdbc:sqlite::memory:", java.util.Properties())
    List("records (seq integer primary key autoincrement, id integer not null unique, tenant text not null, " +
      "kind text not null, title text not null)",
      "shares (seq integer primary key autoincrement, record integer not null, tenant text not null, " +
        "unique (record, tenant))",
      "expiries (seq integer primary key autoincrement, record integer not null, tenant text not null, " +
        "until integer not null, unique (record, tenant))",
      "events (seq integer primary key autoincrement, event text not null)")
      .foreach(table => Using.resource(conn.createStatement())(_.executeUpdate(s"create table $table")))
    val db = Db(conn, select)
    db.synchronized(db.insert(t.store))
    t.events.foreach(db.logEvent)
    db

  /** A database holding the store, used once and closed. */
  def using[A](s: CrmStore, select: Search => (String, List[Any]) = selecting)(f: Db => A): A =
    Using.resource(holding(Tables(s, Nil), select))(f)(using Releasable)

  private object Releasable extends Using.Releasable[Db]:
    def release(db: Db): Unit = db.close()
