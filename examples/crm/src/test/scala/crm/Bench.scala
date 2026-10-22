package crm

/** What the run-time checks cost per request: `sbt "crm/Test/runMain crm.benchReads 100000"`. The read
  * side (ReadContract's code on SQLite, its check, the port's check) against the same SQL and filter
  * with no FrFlow.
  */
@main def benchReads(n: Int): Unit =
  val tenants = (0 until 100).map(i => TenantId(s"t$i"))
  val records = (1 to n).toList.map(i => CrmRecord(i, tenants(i % 100), if i % 2 == 0 then Kind.Deal else Kind.Contact, s"record $i"))
  val shareRows = (1 to n by 50).toList.map(i => Share(i, tenants((i + 1) % 100)))
  val db = Db.of(records, shareRows)
  val ann = Account("ann@t7", tenants(7))
  val read = readSide(db)
  def plain(u: Account, q: Search) =
    val ss = db.shares().toSet
    db.recordsMatching(q).filter(r => r.tenant == u.tenant || ss(Share(r.id, u.tenant)))
  def time(label: String, f: () => Any): Double =
    (1 to 5).foreach(_ => f()) // warm up
    val runs = 10
    val t0 = System.nanoTime
    (1 to runs).foreach(_ => f())
    val ms = (System.nanoTime - t0) / 1e6 / runs
    println(f"$label%-34s $ms%8.2f ms per request")
    ms
  // The same proven code with no checks: what the checks add.
  val unchecked: (Account, Search) => List[CrmRecord] = (u, q) =>
    val ss = db.shares()
    frflow.Bindings.within(List(shares.bind(ss), expiries.bind(Nil), clock.bind(BigInt(0)), database.bind(db),
        fetch.bind((u: Account, q: Search) => db.recordsMatching(q))))(
      search.lifted.value.asInstanceOf[(Account, Search) => List[CrmRecord]](u, q))
  for q <- List(Search.ById(4207), Search.OfKind(Kind.Deal)) do
    val a = time(s"read side, checked, $q", () => read(ann, q))
    val b = time(s"same code, unchecked, $q", () => unchecked(ann, q))
    val c = time(s"hand-written SQL and filter, $q", () => plain(ann, q))
    println(f"  the checks add ${(a - b) / b * 100}%.0f%%; the proven code against hand-written: ${(b - c) / c * 100}%.0f%%")

/** What a write and the read side's start cost as the store grows: `sbt "crm/Test/runMain crm.benchWrites 32000"`. */
@main def benchWrites(n: Int): Unit =
  val tenants = (0 until 100).map(i => TenantId(s"t$i"))
  val records = (1 to n).toList.map(i => CrmRecord(i, tenants(i % 100), Kind.Deal, s"record $i"))
  val db = Db.of(records, (1 to n by 50).toList.map(i => Share(i, tenants((i + 1) % 100))))
  val ann = Account("ann@t7", tenants(7))
  val write = writeSide(db)
  def ms(f: => Any) = { val t0 = System.nanoTime; f; (System.nanoTime - t0) / 1e6 }
  (1 to 3).foreach(i => write(WriteCmd(ann, Change.Add(CrmRecord(n + i, tenants(7), Kind.Deal, "warm")))))
  val w = (1 to 10).map(i => ms(write(WriteCmd(ann, Change.Add(CrmRecord(n + 100 + i, tenants(7), Kind.Deal, "new")))))).sum / 10
  var read: (Account, Search) => List[CrmRecord] = null
  val start = ms { read = readSide(db) }
  val first = ms(read(ann, Search.ById(7)))
  val next = (1 to 10).map(_ => ms(read(ann, Search.ById(7)))).sum / 10
  println(f"$n%7d records: a write $w%8.1f ms; the read side's start $start%8.1f ms, its first read $first%8.1f ms, a read after $next%8.1f ms")
