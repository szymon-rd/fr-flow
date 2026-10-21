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
    intercept[ContractViolation](readContract.enforce(leaky)(shares.bind(shareTable))(ann, Search.Everything))
  }

  test("the knowledge base is proven, from tenant isolation to the contract") {
    assume(Lake(Paths.get(".")).available, "lake is not available")
    val root = Files.createTempDirectory("crm")
    Files.copy(Paths.get("examples/crm/IDEA.md"), root.resolve("IDEA.md"))
    val w = Workflow(knowledge, Workspace(root, Paths.get("lean").toAbsolutePath.toString))
    assertEquals(w.check().map((n, c) => n.id -> c.status),
      List("TenantIsolation" -> "proven", "ReadApi" -> "proven", "Accounts" -> "proven", "ReadContract" -> "proven"))
  }
