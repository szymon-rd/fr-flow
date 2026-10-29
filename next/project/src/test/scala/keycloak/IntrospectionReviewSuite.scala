package keycloak

import cats.effect.IO
import frflow.core.name.{NodeId, RelPath, SymbolName}
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.{Cause, Reading, ReviewState, Subjects}
import frflow.project.Projects
import frflow.project.port.RunCode
import frflow.project.program.Analyse
import java.nio.file.Files
import java.time.Instant

/** Code written beside nodes (owner §38): the introspection's Scala, `introspection`, sits in `Introspection.scala`
  * with four nodes. Only the definitions the Scala refers to are the code `introspectAnswers` governs, so editing
  * `introspection` brings it back for review, and editing a node beside it does not.
  */
class IntrospectionReviewSuite extends munit.CatsEffectSuite:
  private val node = NodeId("introspectAnswers")
  private val elaborated = Projects.elaborated(knowledge)
  private val file = elaborated.theory.code.attached(SymbolName("introspect")).code.scala.toList.flatMap(_.files)
    .map(_.path).find(_.value.endsWith("Introspection.scala")).getOrElse(fail("no Introspection.scala"))
  private val text = Files.readString(Projects.source(file))

  private def analysed(p: Projects.InMemory) =
    val dir = RelPath.parse(file.value.split('/').init.mkString("/")).getOrElse(file)
    Analyse(p.ports, RunCode.inline[IO], Projects.project.copy(sources = List(dir)))(elaborated, Nil)

  private def accepting(s: Subjects): Ledger =
    val unread = Reading(s, Ledger.empty)
    s.inOrder.foldLeft(Ledger.empty)((l, x) => l.add(x.id, Decision.taken(Action.Accept,
      Authorship("ann", Instant.EPOCH, None), Reason("it says what the server must do", Nil), unread.bound(x))))

  private def state(s: Subjects, l: Ledger) = Reading(s, l).standings.get(node).map(st => st.state -> st.causes)

  test("introspectAnswers governs the introspection's Scala in Introspection.scala, not the file's nodes") {
    val gs = frflow.project.code.Governance.of(elaborated.theory, List(file)).getOrElse(node, Nil)
    assertEquals(gs.find(_.path == file), Some(frflow.project.code.Governed.Named(file, List("introspection",
      "lookup"))))
  }

  test("editing a node beside the introspection's Scala brings nothing back; editing the Scala brings it back") {
    val beside = text.replace("An introspection answers only with the realm and user of a session the",
      "An introspection answers only with the realm and the user of a session the")
    val edited = text.replace("a <- accountOf(realm, x.user) if a.enabled", "a <- accountOf(realm, x.user)")
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
