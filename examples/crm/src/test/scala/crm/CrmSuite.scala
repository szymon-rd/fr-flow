package crm

import frflow.*
import java.nio.file.{Files, Paths}

class CrmSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  private val acme = TenantId("acme")
  private val globex = TenantId("globex")
  private val ann = Account("ann@acme", acme)
  private val records = List(
    CrmRecord(1, acme, Kind.Contact, "Ann's contact"),
    CrmRecord(2, globex, Kind.Deal, "Globex deal"),
    CrmRecord(3, globex, Kind.Contact, "Shared contact")
  )
  private val shareTable = List(Share(3, acme))

  private def db(rs: List[CrmRecord] = records, ss: List[Share] = shareTable) = Db.of(rs, ss)

  test("a user sees their company's records and records shared with it, from the database") {
    val read = readSide(db())
    assertEquals(read(ann, Search.Everything).map(_.id), List[BigInt](1, 3))
    assertEquals(read(ann, Search.ById(2)), Nil)
    assertEquals(read(ann, Search.OfKind(Kind.Contact)).map(_.id), List[BigInt](1, 3))
  }

  test("the deals screen calls the read side: shared deals only, never a contact") {
    val shared = records :+ CrmRecord(4, globex, Kind.Deal, "Shared deal")
    val deals = dealSide(db(shared, shareTable :+ Share(4, acme)))
    assertEquals(deals(ann, Search.Everything).map(_.id), List[BigInt](4))
  }

  test("a store the writes could not reach is refused: the reads rely on unique ids") {
    // Two records with one id: a share of Acme's would also show Globex's record with that id.
    val dup = List(CrmRecord(1, acme, Kind.Deal, "Acme deal"), CrmRecord(1, globex, Kind.Deal, "Globex secret"))
    val bob = Account("bob@initech", TenantId("initech"))
    // (SQLite's key refuses two records with one id: the store is bound as the database would not hold it)
    val e = intercept[ContractViolation] {
      val d = Db.of(dup.take(1), List(Share(1, TenantId("initech"))))
      knowledge.service(readContract)(store.bind(dup), shares.bind(List(Share(1, TenantId("initech")))), database.bind(d))(bob, Search.Everything)
    }
    assert(e.getMessage.contains("Accounts relies on CrmWrites"), e.getMessage)
  }

  test("an implementation that leaks another company's records is stopped by its check, on every call") {
    val leaky: (Account, Search) => List[CrmRecord] = (_, _) => records
    val d = db()
    intercept[ContractViolation](knowledge.implement(readContract)(leaky).service(readContract)(store.bind(d.allRecords()), shares.bind(d.shares()), database.bind(d))(ann, Search.Everything))
  }

  test("an implementation that relabels another company's records fails its examples (the cheap check sees the label only)") {
    val relabel: (Account, Search) => List[CrmRecord] = (u, _) => store.value.map(_.copy(tenant = u.tenant))
    assert(knowledge.implement(readContract)(relabel).exampleResults(readContract).exists(_.implementation.exists(_ != "ok")))
  }

  test("a seeded SQL bug (the search's WHERE dropped) is stopped by the port's check; the proofs still hold") {
    val buggy = knowledge.implementProven(recordsByQuery)(storedMatching, (u, q) => database.value.allRecords())
    val d = db()
    val e = intercept[ContractViolation](buggy.service(readContract)(store.bind(d.allRecords()), shares.bind(d.shares()), database.bind(d))(ann, Search.OfKind(Kind.Deal)))
    assert(e.getMessage.contains("RecordsByQuery"), e.getMessage)
    // and the SQL is checked against the define on the port's examples
    assert(buggy.exampleResults(recordsByQuery).exists(_.implementation.exists(_.contains("where the proven define returns"))), buggy.exampleResults(recordsByQuery))
  }

  test("the HTTP API: reads, deals and writes go through the read, deal and write sides") {
    val d = db()
    val server = CrmServer.start(d, 0)
    try
      val base = s"http://127.0.0.1:${server.getAddress.getPort}"
      val client = java.net.http.HttpClient.newHttpClient()
      def call(method: String, path: String, who: Account, body: String = ""): (Int, String) =
        val r = java.net.http.HttpRequest.newBuilder(java.net.URI.create(base + path)).header("X-User", who.email).header("X-Tenant", who.tenant.value)
          .method(method, if body.isEmpty then java.net.http.HttpRequest.BodyPublishers.noBody() else java.net.http.HttpRequest.BodyPublishers.ofString(body)).build()
        val res = client.send(r, java.net.http.HttpResponse.BodyHandlers.ofString())
        (res.statusCode, res.body)
      assertEquals(call("GET", "/records", ann)._1, 200)
      assert(call("GET", "/records", ann)._2.contains("\"id\":3") && !call("GET", "/records", ann)._2.contains("\"id\":2"))
      assertEquals(call("POST", "/records", ann, """{"id":7,"kind":"Deal","title":"Acme deal"}""")._1, 200)
      assert(call("GET", "/deals", ann)._2.contains("\"id\":7"))
      // Ann cannot share Globex's deal: refused, and nothing changes
      assertEquals(call("POST", "/shares", ann, """{"record":2,"to":"acme"}""")._1, 403)
      assert(!call("GET", "/records", ann)._2.contains("\"id\":2"))
    finally server.stop(0)
  }

  test("the expiry job ends shares whose time is up, and nothing else") {
    val d = Db.of(records, List(Share(3, acme), Share(1, globex)), List(Expiry(3, acme, 100)))
    expireOnce(d, 50)
    assertEquals(d.shares().size, 2)
    expireOnce(d, 150)
    assertEquals(d.shares(), List(Share(1, globex)))
    assertEquals(d.allRecords(), records)
    assertEquals(d.expiries(), Nil)
  }

  test("the examples pass against the contract and the implementation") {
    assert(knowledge.exampleResults(readContract).forall(r => r.contract == "ok" && r.implementation.contains("ok")),
      knowledge.exampleResults(readContract))
  }

  test("the knowledge base is proven, from tenant isolation to the contract") {
    assume(Lake(Paths.get(".")).available, "lake is not available")
    val root = Files.createTempDirectory("crm")
    Files.copy(Paths.get("examples/crm/IDEA.md"), root.resolve("IDEA.md"))
    val proofs = Paths.get("examples/crm/lean/Proofs/Crm")
    Files.createDirectories(root.resolve("lean/Proofs/Crm"))
    Files.list(proofs).forEach(f => Files.copy(f, root.resolve("lean/Proofs/Crm").resolve(f.getFileName)))
    val w = Workflow(knowledge, Workspace(root, Paths.get("lean").toAbsolutePath.toString))
    val checked = w.check().map((n, c) => n.id -> c).toMap
    assertEquals(checked.view.mapValues(_.status).toMap, Map("TenantIsolation" -> "proven", "ReadApi" -> "proven", "Accounts" -> "proven",
      "ReadContract" -> "proven", "WritesKeepStore" -> "proven", "StepByStep" -> "proven", "CrmWrites" -> "proven", "WriteContract" -> "proven", "SalesScreen" -> "proven", "DealSearch" -> "proven",
      "RecordsByQuery" -> "proven", "StoreEdits" -> "proven", "SharesExpire" -> "proven", "ExpireJob" -> "proven"))
    // every implementation is proven, and the root holds of each (DealSearch's from ReadContract's promise)
    for c <- List("ReadContract", "WriteContract", "DealSearch", "ExpireJob", "RecordsByQuery", "StoreEdits") do
      assertEquals(checked(c).obligations.filter(o => o.name == "impl" || o.name == "root_impl").map(_.status), List("proven", "proven"), checked(c))
  }

  test("a write changes only what its author's company may change, and the write side checks it") {
    val write = knowledge.service(writeContract)()
    val start = CrmStore(records, shareTable, Nil)
    val added = write(start, WriteCmd(ann, Change.Add(CrmRecord(4, acme, Kind.Deal, "New deal"))))
    assertEquals(added.records.map(_.id), List[BigInt](1, 2, 3, 4))
    // Ann cannot share Globex's deal, nor add a record for Globex: nothing changes
    assertEquals(write(start, WriteCmd(ann, Change.ShareWith(2, acme, None))), start)
    assertEquals(write(start, WriteCmd(ann, Change.Add(CrmRecord(5, globex, Kind.Deal, "Not hers")))), start)
    // an implementation that drops another company's record is stopped by the contract
    val careless: (CrmStore, WriteCmd) => CrmStore = (s, _) => s.copy(records = s.records.filter(_.tenant == acme))
    intercept[ContractViolation](knowledge.implement(writeContract)(careless).service(writeContract)()(start, WriteCmd(ann, Change.Unshare(1, globex))))
  }

  test("a write on the database stores only its record's rows, read back; the store's size does not matter") {
    val d = db()
    val write = writeSide(d)
    write(WriteCmd(ann, Change.Add(CrmRecord(4, acme, Kind.Deal, "New deal"))))
    write(WriteCmd(ann, Change.ShareWith(4, globex, Some(BigInt(100)))))
    assertEquals(d.allRecords().map(_.id), List[BigInt](1, 2, 3, 4))
    assertEquals(d.shares().toSet, Set(Share(3, acme), Share(4, globex)))
    assertEquals(d.expiries(), List(Expiry(4, globex, 100)))
    // sharing again with no end removes the expiry; the job then leaves the share alone
    write(WriteCmd(ann, Change.ShareWith(4, globex, None)))
    assertEquals(d.expiries(), Nil)
    expireOnce(d, 150)
    assert(d.shares().contains(Share(4, globex)))
  }

  test("a database that drops a write is seen on the call: StoreEdits reads the rows back") {
    val d = db()
    val dropping = knowledge.implementProven(storeEdits)(storedAbout, (id, t) => CrmStore(Nil, Nil, Nil))
    val e = intercept[ContractViolation](dropping.service(storeEdits)(database.bind(d))(BigInt(1), CrmStore(records, Nil, Nil)))
    assert(e.getMessage.contains("StoreEdits"), e.getMessage)
  }

  test("a governed file that changes the database past a port is a warning; the wired adapter methods are what is counted as checked") {
    val root = Files.createTempDirectory("crm-bypass")
    Files.copy(Paths.get("examples/crm/IDEA.md"), root.resolve("IDEA.md"))
    val src = Paths.get("examples/crm/src/main/scala/crm")
    Files.createDirectories(root.resolve("src/main/scala/crm"))
    Files.list(src).forEach(f => Files.copy(f, root.resolve("src/main/scala/crm").resolve(f.getFileName)))
    val w = Workflow(knowledge, Workspace(root, Paths.get("lean").toAbsolutePath.toString))
    assertEquals(w.bypasses, Nil)
    val server = root.resolve("src/main/scala/crm/Server.scala")
    Files.writeString(server, Files.readString(server).replace("server.start()", "db.insert(Nil, Nil, Nil)\n    server.start()"))
    assert(w.bypasses.exists(_.contains("changes the outside directly (.insert")), w.bypasses)
  }

  test("SQL that is right on the examples' data but drops rows on more is found on varied data") {
    // The port's examples store two records: a LIMIT 2 passes them all.
    val limited = knowledge.implementProven(recordsByQuery)(storedMatching, (u, q) => database.value.recordsMatching(q).take(2))
    assert(limited.exampleResults(recordsByQuery).filter(r => r.example.expected && !r.example.note.startsWith("generated")).forall(_.implementation.contains("ok")))
    assert(limited.generated(recordsByQuery).exists(_.implementation.exists(_.contains("where the proven define returns"))), limited.generated(recordsByQuery))
    assertEquals(knowledge.generated(recordsByQuery), Nil)
  }
