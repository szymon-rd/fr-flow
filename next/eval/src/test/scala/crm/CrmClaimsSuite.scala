package crm

import frflow.core.expr.Exprs
import frflow.core.name.{DefName, SymbolName}
import frflow.core.spec.CallForm
import rooms.RoomsIr

/** crm's claims in the owner's forms, as the analyses read them: one relating its Definition to another applied to
  * the same inputs (the one on the left of its equation is the one it reads as a call of), and one about a program,
  * a run from the world before. (Their Lean, byte for byte as today's, is `next-proof`'s.)
  */
class CrmClaimsSuite extends munit.FunSuite:
  test("saveWrite reads as a call of `save`, on the left of its equation; `write` on the same inputs is a mention") {
    val call = RoomsIr.call(saveWrite.statement)
    assertEquals(call.definition, SymbolName("save"))
    assertEquals(call.posted.value.params.map(_.hint), List("s", "w"))
    val mentions = Exprs.mentions(call.posted.value.body)
    assert(mentions.symbols.contains(SymbolName("write")), mentions)
    assert(mentions.defines.toSet.subsetOf(Set(DefName("aboutRecord"), DefName("about"))), mentions)
  }

  test("expiryJob, a run from the world before: it reads as a run of runExpiry, its post over now, result, before, " +
    "after, with no failing side") {
    RoomsIr.call(expiryJob.statement) match
      case CallForm.Run(op, post, failure) =>
        assertEquals((op, post.value.params.map(_.hint), failure), (SymbolName("runExpiry"),
          List("now", "result", "before", "after"), None))
      case other => fail(other.toString)
  }

  test("a claim applying its Definition to its leading variables wherever it mentions it reads as its call: the " +
    "write and read contracts") {
    assertEquals(List(writeContract, readContract, dealSearch).map(n => RoomsIr.call(n.statement).definition),
      List(SymbolName("write"), SymbolName("read"), SymbolName("deals")))
  }

  test("a claim relating the screens to what the CRM holds over every record reads as no call") {
    assertEquals(RoomsIr.elaborated(visibility.statement).call, None)
  }
