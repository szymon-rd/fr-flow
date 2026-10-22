package crm

/** The CRM's event log, in its database: every write the write side saved and every run of the expiry
  * job, in order. It is the CRM's history (CrmRun); the read side binds it as `history`. WriteSideWiring
  * governs this file.
  */
extension (db: Db)
  private def eventTable(): Unit = db.conn.createStatement().executeUpdate(
    "create table if not exists events (seq integer primary key autoincrement, event text not null, email text, tenant text, " +
      "record integer, owner text, kind text, title text, target text, until integer, at integer)")

  /** Appends an event to the log. */
  def logEvent(e: Event): Unit = db.synchronized {
    eventTable()
    val st = db.conn.prepareStatement(
      "insert into events (event, email, tenant, record, owner, kind, title, target, until, at) values (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)")
    def set(i: Int, v: Any): Unit = v match
      case n: BigInt => st.setLong(i, n.toLong)
      case null      => st.setNull(i, java.sql.Types.NULL)
      case x         => st.setObject(i, x)
    val row: List[Any] = e match
      case Event.Expired(now) => List("expired", null, null, null, null, null, null, null, null, now)
      case Event.Wrote(WriteCmd(by, c)) =>
        val who = List("wrote", by.email, by.tenant.value)
        c match
          case Change.Add(r)               => who ++ List(r.id, r.tenant.value, r.kind.toString, r.title, null, null, null)
          case Change.ShareWith(id, to, u) => who ++ List(id, null, "share", null, to.value, u.orNull, null)
          case Change.Unshare(id, to)      => who ++ List(id, null, "unshare", null, to.value, null, null)
    row.zipWithIndex.foreach((v, i) => set(i + 1, v))
    st.executeUpdate()
  }

  /** The log, in order. */
  def events(): List[Event] =
    eventTable()
    db.rows("select * from events order by seq") { rs =>
      def num(k: String) = Option(rs.getObject(k)).map(_ => BigInt(rs.getLong(k)))
      if rs.getString("event") == "expired" then Event.Expired(num("at").get)
      else
        val by = Account(rs.getString("email"), TenantId(rs.getString("tenant")))
        val id = num("record").get
        Event.Wrote(WriteCmd(by, rs.getString("kind") match
          case "share"   => Change.ShareWith(id, TenantId(rs.getString("target")), num("until"))
          case "unshare" => Change.Unshare(id, TenantId(rs.getString("target")))
          case k         => Change.Add(CrmRecord(id, TenantId(rs.getString("owner")), Kind.valueOf(k), rs.getString("title")))))
    }
