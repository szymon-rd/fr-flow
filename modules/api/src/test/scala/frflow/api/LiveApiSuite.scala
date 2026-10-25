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
  private def ledger(d: Path) = JsonStore.ledger(project(d).resolve(".frflow/ledger.json")).flatMap(_.load)
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

  dir.test("rejecting a proposal records it with the proposals resting on it, signed") { d =>
    val why = "a shelf is not where picked books come from"
    for
      live <- api(d)
      done <- live.decide(Decide.Reject(NodeId("FromList"), why), dev)
      v <- live.view
    yield
      assertEquals(done.map(_.decisions.map(_.node)), Right(List(NodeId("FromList"), NodeId("Pick"))))
      assertEquals(v.node(NodeId("FromList")).map(_.state), Some(ReviewState.Rejected))
      assertEquals(v.unsigned, Nil)
  }

  dir.test("a refusal records nothing; who decides comes from --as, FRFLOW_AS or the key's filed name") { d =>
    for
      live <- api(d)
      nobody <- live.developer(None)
      noNodes <- live.decide(Decide.Accept(Nil, "nothing at all to accept"), dev)
      unknown <- live.decide(Decide.Accept(List(NodeId("Nope")), "it holds as written"), dev)
      filed <- IO.blocking(Files.exists(project(d).resolve(".frflow/keys")))
      l <- ledger(d)
      fromEnv <- api(d, "FRFLOW_AS" -> "ci-dev").flatMap(_.developer(None))
      named <- api(d, "FRFLOW_AS" -> "ci-dev").flatMap(_.developer(Some("demo")))
    yield
      assertEquals(nobody, Left(Refusal.NoDeveloper))
      assertEquals(noNodes, Left(Refusal.NoNodes))
      assertEquals(unknown, Left(Refusal.UnknownNode(NodeId("Nope"))))
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

  dir.test("IDEA.md is a decision: written, accepted (signed), then the root; a change to it brings it back") { d =>
    import frflow.{KnowledgeBase, Node, True}
    val empty = KnowledgeBase("Toy", idea = "IDEA.md")()
    val root = Node.claim("ToyRoot", "A reader borrows exactly the books on the shelf that nobody else holds.",
      why = "The idea's purpose.")(True)
    def at(kb: KnowledgeBase) = LiveApi(kb, Workspace(project(d), "../lean"), Map("FRFLOW_KEY" -> d.resolve("signing.key").toString))
    val idea = "# Toy\n\nA shelf of books readers borrow.\n\n## Borrowing\nA reader borrows a book nobody holds.\n"
    def write(text: String) = IO.blocking { Files.createDirectories(project(d)); Files.writeString(project(d).resolve("IDEA.md"), text) }
    for
      live <- at(empty)
      before <- live.view
      _ <- write(idea)
      written <- live.view
      accepted <- live.decide(Decide.Accept(List(IdeaReview.Id), "it says what the shelf is for"), dev)
      confirmed <- live.view
      withRoot <- at(KnowledgeBase("Toy", idea = "IDEA.md")(root))
      proposed <- withRoot.view
      _ <- write(idea.replace("A reader borrows a book nobody holds.", "A reader borrows at most three books nobody holds."))
      changed <- withRoot.view
      l <- ledger(d)
    yield
      assertEquals((before.annotated.idea, before.nodes, before.ok), (None, Nil, false))
      assertEquals(written.annotated.idea.map(_.state), Some(ReviewState.Proposed))
      assertEquals(Inbox.of(written).idea.map(_.state), Some(ReviewState.Proposed))
      assertEquals(accepted.map(_.decisions.map(_.node)), Right(List(IdeaReview.Id)))
      assert(l.history(IdeaReview.Id).headOption.exists(_.sig.isDefined), l)
      assertEquals((confirmed.annotated.idea.map(_.state), confirmed.warnings), (Some(ReviewState.Accepted), Nil))
      val r = proposed.node(NodeId("ToyRoot")).get
      assertEquals((r.state, r.review.waitsFor), (ReviewState.Proposed, None))
      assertEquals(changed.annotated.idea.map(_.state), Some(ReviewState.Review))
      assertEquals(changed.node(NodeId("ToyRoot")).flatMap(_.review.waitsFor), Some(IdeaReview.Id))
  }
