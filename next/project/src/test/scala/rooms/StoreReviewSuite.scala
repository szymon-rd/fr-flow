package rooms

import cats.effect.IO
import frflow.core.name.{NodeId, RelPath, SymbolName}
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.{Cause, Reading, ReviewState, Subjects}
import frflow.project.Projects
import frflow.project.port.RunCode
import frflow.project.program.Analyse
import java.time.Instant

/** What a store added beside rooms brings back for review (owner §33): no statement that does not read it, its code
  * included; the calendar's code is its own file, not the file it is attached in.
  */
class StoreReviewSuite extends munit.CatsEffectSuite:
  private val grant = NodeId("grantWhenNoOverlap")
  private val attached = Projects.rooms.theory.code.attached(SymbolName("granted"))

  /** Analysed with the files' own directories as the sources, so their text is read. */
  private def analysed(p: Projects.InMemory, m: frflow.dsl.kb.FrModel, files: List[RelPath]) =
    val dirs = files.map(f => RelPath.parse(f.value.split('/').init.mkString("/")).getOrElse(f)).distinct
    Analyse(p.ports, RunCode.inline[IO], Projects.project.copy(sources = dirs))(Projects.elaborated(m), Nil)

  private def accepting(s: Subjects): Ledger =
    val unread = Reading(s, Ledger.empty)
    s.inOrder.foldLeft(Ledger.empty)((l, x) => l.add(x.id, Decision.taken(Action.Accept,
      Authorship("ann", Instant.EPOCH, None), Reason("it says what the service must do", Nil), unread.bound(x))))

  test("the calendar's code is the files it refers to, not the file of its own parameters (where it is attached)") {
    val files = attached.code.scala.toList.flatMap(_.files)
    assertEquals(files.map(_.toString.split('/').last), List("Calendar.scala"))
    assert(!files.contains(attached.writtenIn), files)
  }

  test("rooms with the log's nodes added keeps the calendar's claim accepted; a change to the calendar brings it " +
    "back") {
    val calendar = attached.code.scala.toList.flatMap(_.files).head
    val model = Projects.elaborated(Logged.withNodes()).theory.code.attached(SymbolName("granted")).writtenIn
    def state(s: Subjects, l: Ledger) = Reading(s, l).standings.get(grant).map(st => st.state -> st.causes)
    for
      p      <- Projects.inMemory(Map(calendar -> "final class Calendar", model -> "val rooms = FrModel(...)"))
      before <- analysed(p, Logged.withNodes(), List(calendar, model))
      ledger  = accepting(before.subjects)
      _      <- p.files.writeIfChanged(model, "val rooms = FrModel(..., logMatchesModel, ...)")
      logged <- analysed(p, Logged.withNodes(Logged.log*), List(calendar, model))
      _      <- p.files.writeIfChanged(calendar, "final class Calendar(held: RoomBookings)")
      moved  <- analysed(p, Logged.withNodes(Logged.log*), List(calendar, model))
    yield
      assertEquals(state(logged.subjects, ledger), Some(ReviewState.Accepted -> Nil))
      assertEquals(state(moved.subjects, ledger), Some(ReviewState.Review -> List(Cause.Code)))
  }
