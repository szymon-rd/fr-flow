package crm

/** Tables as the CRM's history leaves them, for the tests' runs of the database's operations: what the database's
  * rules say (`crmRun`, `oneRowPerKey`), in plain Scala, each event saved by the write side or run by the expiry job
  * in turn from the empty tables, as `stepOf` says.
  */
object History:
  def tables(events: List[Event]): Tables =
    Tables(events.foldLeft(CrmStore(Nil, Nil, Nil))(step), events)

  private def step(s: CrmStore, e: Event): CrmStore = e match
    case Event.Wrote(w)     => replace(s, about(w), aboutRecord(write(s, w), about(w)))
    case Event.Expired(now) =>
      val t = expired(s, now)
      (ids(s) ++ ids(t)).foldLeft(s)((x, id) =>
        if aboutRecord(s, id) != aboutRecord(t, id) then replace(x, id, aboutRecord(t, id)) else x)

  private def about(w: WriteCmd): BigInt = w.change match
    case Change.Add(r)             => r.id
    case Change.ShareWith(id, _, _) => id
    case Change.Unshare(id, _)     => id

  private def aboutRecord(s: CrmStore, id: BigInt): CrmStore =
    CrmStore(s.records.filter(_.id == id), s.shares.filter(_.record == id), s.expiries.filter(_.record == id))

  private def replace(s: CrmStore, id: BigInt, rows: CrmStore): CrmStore =
    CrmStore(s.records.filterNot(_.id == id) ++ rows.records, s.shares.filterNot(_.record == id) ++ rows.shares,
      s.expiries.filterNot(_.record == id) ++ rows.expiries)

  private def ids(s: CrmStore): List[BigInt] = s.records.map(_.id) ++ s.shares.map(_.record) ++ s.expiries.map(_.record)

  private def write(s: CrmStore, w: WriteCmd): CrmStore =
    val own = (id: BigInt) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant)
    val others = (id: BigInt, to: TenantId) => s.expiries.filterNot(e => e.record == id && e.to == to)
    w.change match
      case Change.Add(r) if r.tenant == w.by.tenant && !s.records.exists(_.id == r.id) =>
        s.copy(records = s.records :+ r)
      case Change.ShareWith(id, to, until) if own(id) => CrmStore(s.records,
          s.shares.filterNot(_ == Share(id, to)) :+ Share(id, to),
          others(id, to) ++ until.map(Expiry(id, to, _)).toList)
      case Change.Unshare(id, to) if own(id) =>
        CrmStore(s.records, s.shares.filterNot(_ == Share(id, to)), others(id, to))
      case _ => s

  private def expired(s: CrmStore, now: BigInt): CrmStore =
    val ended = (record: BigInt, to: TenantId) =>
      s.expiries.exists(e => e.record == record && e.to == to && e.until <= now)
    CrmStore(s.records, s.shares.filterNot(sh => ended(sh.record, sh.to)),
      s.expiries.filterNot(e => ended(e.record, e.to)))
