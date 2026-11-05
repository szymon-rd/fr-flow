package frflow.testing.ported

import crm.*
import frflow.core.name.SymbolName
import frflow.core.spec.CallForm
import rooms.RoomsIr

/** crm's claims in the owner's forms, as the analyses read them: one relating its Definition to another applied to
  * the same inputs (the one on the left of its equation is the one it reads as a call of), and one about a program,
  * a run from the world before. (Their Lean, byte for byte as today's, is `proof`'s.)
  */
class CrmClaimsSuite extends munit.FunSuite:
  test("saveWrite, a run from the world it holds in: it reads as a run of save, its post over w, result, world, " +
    "after, with no failing side") {
    RoomsIr.call(saveWrite.alone) match
      case CallForm.Run(op, post, failure) =>
        assertEquals((op, post.value.params.map(_.hint), failure), (SymbolName("save"),
          List("w", "result", "world", "after"), None))
      case other => fail(other.toString)
  }

  test("expiryJob, a run from the world it holds in: it reads as a run of runExpiry, its post over now, result, " +
    "world, after, with no failing side") {
    RoomsIr.call(expiryJob.alone) match
      case CallForm.Run(op, post, failure) =>
        assertEquals((op, post.value.params.map(_.hint), failure), (SymbolName("runExpiry"),
          List("now", "result", "world", "after"), None))
      case other => fail(other.toString)
  }

  test("a claim applying its Definition to its leading variables wherever it mentions it reads as its call: the " +
    "write and read contracts") {
    assertEquals(List(writeContract, readContract, dealSearch).map(n => RoomsIr.call(n.alone).definition),
      List(SymbolName("write"), SymbolName("read"), SymbolName("deals")))
  }

  test("a claim relating the screens to what the CRM holds over every record reads as no call") {
    assertEquals(RoomsIr.elaborated(visibility.alone).call, None)
  }
