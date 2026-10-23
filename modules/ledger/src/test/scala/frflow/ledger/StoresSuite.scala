package frflow
package ledger

import frflow.protocol.*
import java.nio.file.Files
import java.time.Instant

/** The files the ledger module keeps: the ledger, and the requests the agent answers. */
class StoresSuite extends munit.FunSuite:

  test("an answer goes to the request named, or to the open request on a node, or starts one from the agent") {
    val file = Files.createTempDirectory("frflow-requests").resolve(".frflow/requests.json")
    assertEquals(RequestStore.load(file), Nil)
    val now = Instant.parse("2026-01-01T00:00:00Z")
    assertEquals(RequestStore.answer(file, "Nowhere", "text", _ => false, now), Left("no request or node Nowhere"))
    val made = RequestStore.answer(file, "Pick", "Picking is now quicker.", _ == "Pick", now)
    assert(made.isRight, made)
    val List(r) = RequestStore.load(file): @unchecked
    assertEquals((r.node, r.by, r.status, r.answer), (Some(NodeId("Pick")), "agent", RequestStatus.Answered, Some("Picking is now quicker.")))
    assertEquals(RequestStore.answer(file, r.id.value, "Said again.", _ => false, now), Right(r.id))
    assertEquals(RequestStore.load(file).map(_.answer), List(Some("Said again.")))
  }

  test("the ledger survives its file") {
    val file = Files.createTempDirectory("frflow-ledger").resolve(".frflow/ledger.json")
    assertEquals(LedgerStore.load(file), Ledger.empty)
    val l = Ledger.empty.add(NodeId("Root"), Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", "it is the idea", chain = Chain("c")))
    LedgerStore.save(file, l)
    assertEquals(LedgerStore.load(file), l)
    Files.writeString(file, "{ not json")
    intercept[IllegalArgumentException](LedgerStore.load(file))
  }
