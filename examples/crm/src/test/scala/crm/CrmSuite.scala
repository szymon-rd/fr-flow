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

  test("a user sees their company's records and records shared with it") {
    val read = readSide(records, shareTable)
    assertEquals(read(ann, Search.Everything).map(_.id), List(1L, 3L))
    assertEquals(read(ann, Search.ById(2)), Nil)
    assertEquals(read(ann, Search.OfKind(Kind.Contact)).map(_.id), List(1L, 3L))
  }

  test("an implementation that leaks another company's records is stopped by its contract") {
    val leaky: (Account, Search) => List[CrmRecord] = (_, _) => records
    intercept[ContractViolation](knowledge.implement(readContract)(leaky).service(readContract)(store.bind(records), shares.bind(shareTable))(ann, Search.Everything))
  }

  test("an implementation that relabels another company's records is stopped by its contract") {
    val relabel: (Account, Search) => List[CrmRecord] = (u, _) => records.map(_.copy(tenant = u.tenant))
    intercept[ContractViolation](knowledge.implement(readContract)(relabel).service(readContract)(store.bind(records), shares.bind(shareTable))(ann, Search.Everything))
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
      "ReadContract" -> "proven", "WritesKeepStore" -> "proven", "CrmWrites" -> "proven", "WriteContract" -> "proven"))
    // both implementations are proven, and the root holds of each
    for c <- List("ReadContract", "WriteContract") do
      assertEquals(checked(c).obligations.filter(o => o.name == "impl" || o.name == "root_impl").map(_.status), List("proven", "proven"), checked(c))
  }

  test("a write changes only what its author's company may change, and the write side checks it") {
    val write = writeSide()
    val start = CrmStore(records, shareTable)
    val added = write(start, WriteCmd(ann, Change.Add(CrmRecord(4, acme, Kind.Deal, "New deal"))))
    assertEquals(added.records.map(_.id), List(1L, 2L, 3L, 4L))
    // Ann cannot share Globex's deal, nor add a record for Globex: nothing changes
    assertEquals(write(start, WriteCmd(ann, Change.ShareWith(2, acme))), start)
    assertEquals(write(start, WriteCmd(ann, Change.Add(CrmRecord(5, globex, Kind.Deal, "Not hers")))), start)
    // an implementation that drops another company's record is stopped by the contract
    val careless: (CrmStore, WriteCmd) => CrmStore = (s, _) => s.copy(records = s.records.filter(_.tenant == acme))
    intercept[ContractViolation](knowledge.implement(writeContract)(careless).service(writeContract)()(start, WriteCmd(ann, Change.Unshare(1, globex))))
  }
