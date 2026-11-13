package frflow.project.services

import frflow.core.name.NodeId
import frflow.dsl.kb.FrModel
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{CheckStatus, Finding, ObligationStatus}
import scala.annotation.experimental
import scala.concurrent.duration.*

/** Rooms' walk-through, replayed through the check on Rocq with rooms' own proof files: the model as it is, and the
  * two changes the README shows (`rooms.walkthrough`), each caught where the README says it is.
  */
@experimental class RoomsWalkthroughSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  private val purpose = List("bookWhenFree", "acceptWhenFree", "neverOverlap")
  private val code = List("storeWhenNoOverlap", "answerWhenNoOverlap")

  private def checked(model: FrModel) =
    Ported.run(Projects.elaborated(model), Nil, Ported.proofs("rooms", "Rooms")).map(a =>
      (a, (purpose ++ code).map(n => n -> a.current(NodeId(n)).fold(CheckStatus.Unchecked)(_.status)).toMap))

  test("as it is: the class meets what it checks, and the purpose follows by the proof files".tag(Live)) {
    checked(_root_.rooms.rooms).map((a, status) =>
      assertEquals(status.values.toSet, Set[CheckStatus](CheckStatus.Proven), Ported.table(a)))
  }

  test("the code forgets a comparison: its own claims are not proven of it, nor is the purpose".tag(Live)) {
    checked(_root_.rooms.walkthrough.forgetful).map { (a, status) =>
      (code ++ purpose).foreach(n => assertEquals(status(n), CheckStatus.Open, Ported.table(a)))
      code.foreach(n => assert(a.current(NodeId(n)).exists(_.results.exists(r =>
        r.name == ObligationName.Impl && r.status == ObligationStatus.Open && r.messages.nonEmpty)), Ported.table(a)))
    }
  }

  test("an overlap misread below the purpose: the code meets its claims, the step to the purpose fails".tag(Live)) {
    checked(_root_.rooms.walkthrough.misread).map { (a, status) =>
      code.foreach(n => assertEquals(status(n), CheckStatus.Proven, Ported.table(a)))
      purpose.foreach { n =>
        assertEquals(status(n), CheckStatus.Open, Ported.table(a))
        assert(a.current(NodeId(n)).exists(_.findings.exists {
          case Finding.LemmasDoNotBuild(_) => true
          case _                           => false
        }), Ported.table(a))
      }
    }
  }
