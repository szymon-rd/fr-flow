package crm

import cats.effect.IO
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.{Cause, Reading, ReviewState, Subjects}
import frflow.project.Projects
import frflow.project.port.RunCode
import frflow.project.program.Analyse
import java.nio.file.Files
import java.time.Instant

/** Code written beside nodes (owner §38): the database's Scala, `SqliteDatabase`, sits in `Database.scala` with the
  * database's model and its nodes. Only the definitions the Scala given the model refers to are the code
  * `tablesModel` governs (that nothing but the code changes the tables), so editing `SqliteDatabase` brings it back
  * for review, and editing a node beside it does not.
  */
class DatabaseReviewSuite extends munit.CatsEffectSuite:
  private val node = NodeId("tablesModel")
  private val elaborated = Projects.elaborated(knowledge)
  private val file = elaborated.theory.code.implemented(databaseModel.name).files.map(_.path)
    .find(_.value.endsWith("Database.scala")).getOrElse(fail("no Database.scala"))
  private val text = Files.readString(Projects.source(file))

  private def analysed(p: Projects.InMemory) =
    val dir = RelPath.parse(file.value.split('/').init.mkString("/")).getOrElse(file)
    Analyse(p.ports, RunCode.inline[IO], Projects.project.copy(sources = List(dir)))(elaborated, Nil)

  private def accepting(s: Subjects): Ledger =
    val unread = Reading(s, Ledger.empty)
    s.inOrder.foldLeft(Ledger.empty)((l, x) => l.add(x.id, Decision.taken(Action.Accept,
      Authorship("ann", Instant.EPOCH, None), Reason("it says what the database must do", Nil), unread.bound(x))))

  private def state(s: Subjects, l: Ledger) = Reading(s, l).standings.get(node).map(st => st.state -> st.causes)

  test("tablesModel governs the database's Scala in Database.scala, not the file's nodes") {
    val gs = frflow.project.code.Governance.of(elaborated.theory, List(file)).getOrElse(node, Nil)
    val names = gs.collect { case frflow.project.code.Governed.Named(`file`, ns) => ns }.flatten
    assert(names.contains("SqliteDatabase") && !names.exists(n => List("tablesModel", "runsOneAtATime",
      "databaseModel").contains(n)), names)
  }

  test("editing a node beside the database's Scala brings nothing back; editing the Scala brings it back") {
    val beside = text.replace("Runs on the database never interleave", "Runs on the database never overlap")
    val edited = text.replace("IO.blocking(db.load())", "IO.blocking(db.load()).map(identity)")
    assert(beside != text && edited != text)
    for
      p      <- Projects.inMemory(Map(file -> text))
      before <- analysed(p)
      ledger  = accepting(before.subjects)
      _      <- p.files.writeIfChanged(file, beside)
      nodes  <- analysed(p)
      _      <- p.files.writeIfChanged(file, edited)
      code   <- analysed(p)
    yield
      assertEquals(state(nodes.subjects, ledger), Some(ReviewState.Accepted -> Nil))
      assertEquals(state(code.subjects, ledger), Some(ReviewState.Review -> List(Cause.Code)))
  }
