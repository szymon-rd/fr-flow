package crm

import java.sql.{Connection, DriverManager}

/** The CRM's records and shares in SQLite: the adapter behind the RecordsByQuery port. What it
  * returns is checked against the port on every call (`checkedBy`), and against the proven `define`
  * the port is decided with on every combination of the port's examples.
  */
final class Db private (val conn: Connection):
  conn.createStatement().executeUpdate(
    "create table if not exists records (id integer primary key, tenant text not null, kind text not null, title text not null)")
  conn.createStatement().executeUpdate(
    "create table if not exists shares (record integer not null, tenant text not null, primary key (record, tenant))")
  conn.createStatement().executeUpdate(
    "create table if not exists expiries (record integer not null, tenant text not null, until integer not null, primary key (record, tenant))")

  private def rows[T](sql: String, args: Any*)(read: java.sql.ResultSet => T): List[T] = synchronized {
    val st = conn.prepareStatement(sql)
    args.zipWithIndex.foreach((a, i) => st.setObject(i + 1, a))
    val rs = st.executeQuery()
    val out = List.newBuilder[T]
    while rs.next() do out += read(rs)
    out.result()
  }
  private def record(rs: java.sql.ResultSet) =
    CrmRecord(BigInt(rs.getLong("id")), TenantId(rs.getString("tenant")), Kind.valueOf(rs.getString("kind")), rs.getString("title"))

  /** The stored records a search asks for, by SQL. */
  def recordsMatching(q: Search): List[CrmRecord] = q match
    case Search.ById(id)   => rows("select * from records where id = ? order by id", id.toLong)(record)
    case Search.OfKind(k)  => rows("select * from records where kind = ? order by id", k.toString)(record)
    case Search.Everything => rows("select * from records order by id")(record)

  def allRecords(): List[CrmRecord] = recordsMatching(Search.Everything)
  def shares(): List[Share] = rows("select record, tenant from shares order by record, tenant")(rs => Share(BigInt(rs.getLong(1)), TenantId(rs.getString(2))))
  def expiries(): List[Expiry] =
    rows("select record, tenant, until from expiries order by record, tenant")(rs => Expiry(BigInt(rs.getLong(1)), TenantId(rs.getString(2)), BigInt(rs.getLong(3))))
  def load(): CrmStore = CrmStore(allRecords(), shares())

  /** Stores `t` in place of what is stored, in one transaction. */
  def save(t: CrmStore): Unit = synchronized {
    conn.setAutoCommit(false)
    try
      conn.createStatement().executeUpdate("delete from records")
      conn.createStatement().executeUpdate("delete from shares")
      val r = conn.prepareStatement("insert into records (id, tenant, kind, title) values (?, ?, ?, ?)")
      t.records.foreach { x => r.setLong(1, x.id.toLong); r.setString(2, x.tenant.value); r.setString(3, x.kind.toString); r.setString(4, x.title); r.executeUpdate() }
      val s = conn.prepareStatement("insert or ignore into shares (record, tenant) values (?, ?)")
      t.shares.foreach { x => s.setLong(1, x.record.toLong); s.setString(2, x.to.value); s.executeUpdate() }
      conn.commit()
    catch
      case e: Exception => conn.rollback(); throw e
    finally conn.setAutoCommit(true)
  }

  def setExpiry(e: Expiry): Unit = synchronized {
    val st = conn.prepareStatement("insert or replace into expiries (record, tenant, until) values (?, ?, ?)")
    st.setLong(1, e.record.toLong); st.setString(2, e.to.value); st.setLong(3, e.until.toLong); st.executeUpdate()
  }

object Db:
  /** A database file (created if missing). */
  def open(path: String): Db = Db(DriverManager.getConnection(s"jdbc:sqlite:$path"))

  /** An in-memory database holding the given records and shares: for examples and tests. */
  def of(records: List[CrmRecord], shares: List[Share] = Nil): Db =
    val db = Db(DriverManager.getConnection("jdbc:sqlite::memory:"))
    db.save(CrmStore(records, shares))
    db
