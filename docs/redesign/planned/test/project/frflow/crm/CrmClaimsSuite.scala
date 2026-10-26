package crm

import frflow.core.expr.Lambda
import frflow.core.name.SymbolName
import frflow.core.spec.Written
import frflow.proof.lean.ExpiryIr
import frflow.proof.lean.print.Print
import rooms.RoomsLean

/** crm's `SaveWrite` and `ExpiryJob` written in the owner's forms, elaborated, and printed as the Lean today's FrFlow
  * generates (`test/proof/resources/crm`); `ExpiryJob`'s post byte for byte as the hand-built IR prints it.
  */
class CrmClaimsSuite extends munit.FunSuite:
  private def post(w: Written[Lambda]): String = Print.expr(ExpiryIr.lowered(w))
  private def specLine: String =
    scala.io.Source.fromResource("crm/ExpiryJob/Spec.lean").getLines().find(_.contains("fun (now : Int)")).get.trim

  test("saveWrite reads as a call of `save`, on the left of its equation; `write` on the same inputs is a mention") {
    assertEquals(RoomsLean.call(saveWrite.statement).definition, SymbolName("save"))
    assertEquals(post(RoomsLean.post(saveWrite.statement)), "fun (s : CrmStore) (w : WriteCmd) => " +
      "((save s w) = (Crm.aboutRecord (write s w) (Crm.about w)))")
  }

  test("ExpiryJob, a run from the world before: it reads as a run of runExpiry, its post over now, result, before, " +
    "after") {
    assertEquals(RoomsLean.call(expiryJob.statement).definition, SymbolName("runExpiry"))
    assertEquals(RoomsLean.post(expiryJob.statement).value.params.map(_.hint), List("now", "result", "before", "after"))
  }

  test("ExpiryJob's post prints byte for byte as the hand-built IR's and as today's Spec.lean") {
    val written = post(RoomsLean.post(expiryJob.statement))
    assertEquals(written, post(ExpiryIr.post))
    assertEquals(written, specLine)
  }
