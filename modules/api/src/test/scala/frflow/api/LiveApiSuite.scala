package frflow.api

import cats.effect.{IO, Resource}
import frflow.check.Workspace
import frflow.fixtures.shelfKb
import frflow.ledger.{JsonStore, KeyStore, Signing}
import frflow.protocol.*
import java.nio.file.{Files, Path}
import java.util.Comparator
import scala.util.Using

/** The live API over a project on disk, deciding with a key of its own: the one path that signs a decision. */
class LiveApiSuite extends munit.CatsEffectSuite:
  /** A directory holding the project and the developer's key, deleted after the test. */
  private val dir = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-live")))(d =>
    IO.blocking(Using.resource(Files.walk(d))(_.sorted(Comparator.reverseOrder()).forEach(Files.delete(_))))))
  private def project(d: Path) = d.resolve("project")
  private def api(d: Path, env: (String, String)*) =
    LiveApi(shelfKb, Workspace(project(d), "../lean"), Map("FRFLOW_KEY" -> d.resolve("signing.key").toString) ++ env)
  private def ledger(d: Path) = JsonStore.make(project(d).resolve(".frflow/ledger.json"), Ledger.empty).flatMap(_.load)
  private val dev = Developer("demo")

  dir.test("accepting records a decision signed with the developer's key, which it files under their name") { d =>
    for
      live <- api(d)
      done <- live.decide(Decide.Accept(List(NodeId("Books")), "books are what the shelf holds"), dev)
      l <- ledger(d)
      keys <- KeyStore.projectKeys(project(d).resolve(".frflow/keys"))
      v <- live.view
      named <- live.developer(None)
    yield
      assertEquals(done.map(_.decisions.map(x => (x.node, x.decision.action))), Right(List(NodeId("Books") -> Action.Accept)))
      assert(Files.isRegularFile(project(d).resolve(".frflow/keys/demo.pub")))
      assert(l.current(NodeId("Books")).exists(_.sig.isDefined), l)
      assertEquals(Signing.unsigned(l, keys), Nil)
      assertEquals(v.unsigned, Nil)
      assert(!v.warnings.exists(w => w.contains("not signed") || w.contains("no developer key")), v.warnings)
      // the name the key is filed under decides from now on
      assertEquals(named, Right(dev))
  }

  dir.test("rejecting a proposal records it with the proposals resting on it, signed; the agent is to replace it") { d =>
    val why = "a shelf is not where picked books come from"
    for
      live <- api(d)
      done <- live.decide(Decide.Reject(NodeId("FromList"), why), dev)
      v <- live.view
    yield
      assertEquals(done.map(_.decisions.map(_.node)), Right(List(NodeId("FromList"), NodeId("Pick"))))
      assertEquals(v.node(NodeId("FromList")).map(_.state), Some(ReviewState.Rejected))
      assertEquals(v.unsigned, Nil)
      assert(Inbox.of(v).forAgent.contains(ForAgent.Replace(NodeId("FromList"), dev.name, why)), Inbox.of(v).forAgent)
  }

  dir.test("the developer asks; the agent answers the request") { d =>
    for
      live <- api(d)
      asked <- live.ask(Some(NodeId("OnlyGood")), "Say what makes an item good.", dev)
      id = asked.fold(r => fail(r.message), _.id)
      answered <- live.answer(id.value, "Books says it: a book is good when it is long enough.")
      v <- live.view
    yield
      assertEquals(answered, Right(id))
      assertEquals(v.requests.map(q => (q.id, q.node, q.status, q.answer)),
        List((id, Some(NodeId("OnlyGood")), RequestStatus.Answered, Some("Books says it: a book is good when it is long enough."))))
  }

  dir.test("a refusal records nothing; who decides comes from --as, FRFLOW_AS or the key's filed name") { d =>
    for
      live <- api(d)
      nobody <- live.developer(None)
      noNodes <- live.decide(Decide.Accept(Nil, "nothing at all to accept"), dev)
      unknown <- live.ask(Some(NodeId("Nope")), "Say more.", dev)
      empty <- live.ask(None, "  ", dev)
      filed <- IO.blocking(Files.exists(project(d).resolve(".frflow/keys")))
      l <- ledger(d)
      fromEnv <- api(d, "FRFLOW_AS" -> "ci-dev").flatMap(_.developer(None))
      named <- api(d, "FRFLOW_AS" -> "ci-dev").flatMap(_.developer(Some("demo")))
    yield
      assertEquals(nobody, Left(Refusal.NoDeveloper))
      assertEquals(noNodes, Left(Refusal.NoNodes))
      assertEquals(unknown, Left(Refusal.UnknownNode(NodeId("Nope"))))
      assertEquals(empty, Left(Refusal.NoText))
      assertEquals((filed, l), (false, Ledger.empty))
      assertEquals((fromEnv, named), (Right(Developer("ci-dev")), Right(dev)))
  }

  dir.test("the model's fingerprint moves when a source of the model changes on disk, and only then") { d =>
    val source = project(d).resolve("src/main/scala/Shelf.scala")
    for
      live <- api(d)
      _ <- IO.blocking { Files.createDirectories(source.getParent); Files.writeString(source, "object Shelf") }
      before <- live.modelFingerprint
      same <- live.modelFingerprint
      _ <- IO.blocking(Files.writeString(source, "object Shelf:\n  val books = 1"))
      after <- live.modelFingerprint
    yield
      assertEquals(same, before)
      assertNotEquals(after, before)
  }
