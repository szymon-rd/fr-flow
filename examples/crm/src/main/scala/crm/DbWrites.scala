package crm

/** Writes to the database: the adapter behind the StoreEdits port. The rows it stores are read back
  * and checked against the port on every call.
  */
extension (db: Db)
  /** What is stored about record `id`, in the order it was stored. */
  def storedRows(id: BigInt): CrmStore = CrmStore(
    db.rows("select * from records where id = ? order by rowid", id.toLong)(db.record),
    db.rows("select record, tenant from shares where record = ? order by rowid", id.toLong)(rs => Share(BigInt(rs.getLong(1)), TenantId(rs.getString(2)))),
    db.rows("select record, tenant, until from expiries where record = ? order by rowid", id.toLong)(rs => Expiry(BigInt(rs.getLong(1)), TenantId(rs.getString(2)), BigInt(rs.getLong(3)))))

  /** Replaces what is stored about record `id` with what `t` holds about it, in one transaction; returns
    * the rows about it, read back.
    */
  def storeAbout(id: BigInt, t: CrmStore): CrmStore = db.synchronized {
    db.conn.setAutoCommit(false)
    try
      for table <- List("records where id", "shares where record", "expiries where record") do
        val d = db.conn.prepareStatement(s"delete from $table = ?"); d.setLong(1, id.toLong); d.executeUpdate()
      db.insert(t.records.filter(_.id == id), t.shares.filter(_.record == id), t.expiries.filter(_.record == id))
      db.conn.commit()
    catch
      case e: Exception => db.conn.rollback(); throw e
    finally db.conn.setAutoCommit(true)
    storedRows(id)
  }
