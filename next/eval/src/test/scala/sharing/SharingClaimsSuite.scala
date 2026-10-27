package sharing

import frflow.core.expr.Exprs
import frflow.core.name.{SymbolName, TypeName}
import frflow.core.spec.{CallForm, FailureClause}
import frflow.core.ty.Ty
import rooms.RoomsIr
import sharing.http.SharingHttp
import sharing.notifications.NotificationsClaims
import sharing.service.SharingClaims

/** sharing's claims in the owner's forms, as the analyses read them: one stating its Definition by another applied to
  * the same inputs, a run whose failing side changes nothing, and a run stating both outcomes. (Their Lean is
  * `next-proof`'s.)
  */
class SharingClaimsSuite extends munit.FunSuite:
  private def failure(c: CallForm): Option[FailureClause] = c match
    case CallForm.Run(_, _, f) => f
    case CallForm.Call(_, _)   => None

  test("canViewContract reads as a call of canView; access, applied to the same inputs, is an ordinary mention") {
    val call = RoomsIr.call(SharingClaims.canViewContract.statement)
    assertEquals(call.definition, SymbolName("canView"))
    assertEquals(call.posted.value.params.map(_.hint), List("lib", "t", "p", "d"))
    assert(Exprs.mentions(call.posted.value.body).symbols.contains(SymbolName("access")))
  }

  test("handleContract: a run of handle, its post over the request, the answer, before and after; a failing run " +
    "changes nothing") {
    val c = RoomsIr.call(SharingHttp.handleContract.statement)
    assertEquals((c.definition, c.posted.value.params.map(_.hint)),
      (SymbolName("handle"), List("r", "result", "before", "after")))
    failure(c) match
      case Some(FailureClause(e, post)) =>
        assertEquals((e, post.value.params.map(_.hint)), (Ty.Data(TypeName("Failure")),
          List("r", "error", "before", "after")))
      case None => fail("no failing side")
  }

  test("deliveryJob, a run of a program of no input with both outcomes: the success side its post, the failing " +
    "side its failure clause") {
    val c = RoomsIr.call(NotificationsClaims.deliveryJob.statement)
    assertEquals((c.definition, c.posted.value.params.map(_.hint)),
      (SymbolName("deliver"), List("result", "before", "after")))
    assertEquals(failure(c).map(f => (f.error, f.post.value.params.map(_.hint))),
      Some((Ty.Data(TypeName("Failure")), List("error", "before", "after"))))
  }

  test("a branch over several operations reads as no call: it is checked as a whole") {
    assertEquals(RoomsIr.elaborated(accessFollowsShares.statement).call, None)
  }
