package frflow.api

import cats.effect.{IO, Resource}
import frflow.api.Opened.id
import frflow.api.node.tests.TestOutcome
import frflow.api.shell.Memory
import frflow.api.view.Listed
import frflow.core.name.RelPath
import frflow.decision.rules.{Command, Refusal}
import frflow.project.port.{ProjectFiles, Records}
import frflow.testing.report.Outcome
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.DecidersFile
import frflow.wire.test.TestsFile
import java.nio.file.Files
import java.security.KeyPairGenerator
import java.util.Base64

/** What an acceptance is decided on, and what may be decided at all: an acceptance is checked and tested afresh (the
  * records on disk are not trusted); a node shown at one version is refused once it moved; a name the key is not
  * listed under is refused first; and the first deciders' list is written from the developer's key.
  */
class AcceptingSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))
  private val accept = Command.Accept(List(nonNegative, sameAbove), "it says what the service must do", Nil, Map.empty)
  private def one(seen: String) = Command.Accept(List(nonNegative), "it says what the service must do", Nil,
    Map(nonNegative -> seen))

  test("an acceptance is tested afresh: a failing report written over as passing is not trusted") {
    for
      ports    <- Opened.ports()
      careless <- Opened.over(Opened.project(Shelf.Careless.kb), ports)
      _        <- Opened.checked(careless.proving.check(None))
      _        <- forged(ports.files)
      shown    <- careless.reading.view
      out      <- careless.deciding.decide(accept, "ann")
    yield
      assertEquals(shown.node(nonNegative).flatMap(_.code).flatMap(_.tests).map(_.outcome), Some(TestOutcome.Passed))
      assert(out match
        case Left(Refusal.CodeFails(_) | Refusal.Within(_, Refusal.CodeFails(_))) => true
        case _                                                                    => false, out)
  }

  test("a node accepted at the version shown is refused once it moved since") {
    for
      api  <- Opened.api(Opened.before)
      seen <- api.reading.view.map(_.node(nonNegative).map(_.review.version).getOrElse(""))
      out  <- api.deciding.decide(one("another"), "ann")
      ok   <- api.deciding.decide(one(seen), "ann")
    yield
      assertEquals(out, Left(Refusal.MovedSinceSeen(nonNegative)))
      assert(ok.isRight, ok)
  }

  test("a confirmation is checked afresh: proofs recorded by another run are not trusted") {
    val confirm = Command.Confirm("a new part makes it as before")
    for
      ports   <- Opened.ports()
      _       <- Opened.over(Opened.before, ports).flatMap(Opened.acceptAll)
      proving <- Opened.over(Opened.project(Shelf.Grown.kb), ports)
      checked <- Opened.checked(proving.proving.check(None))
      failing  = Lean.Proving(checked.nodes.flatMap(_.proof.results.map(_.theorem)).toSet, Set.empty)
      other   <- Memory.api(Opened.session(Opened.project(Shelf.Grown.kb), ports, failing))
      shown   <- other.reading.view
      out     <- other.deciding.decide(confirm, "ann")
      ok      <- proving.deciding.preview(confirm, "ann")
    yield
      assertEquals(shown.node(nonNegative).map(_.review.notMechanical), Some(None))
      assertEquals(out, Left(Refusal.NothingToConfirm))
      assertEquals(ok.map(_.recorded.map(_._1)), Right(List(nonNegative)))
  }

  test("a name the key is not listed under is refused before anything is checked") {
    for
      api  <- Opened.api(Opened.before, lean = Lean.Absent)
      seen <- api.deciding.preview(accept, "mallory")
      done <- api.deciding.decide(accept, "mallory")
    yield assertEquals((seen, done), (Left(Refusal.NotADecider("mallory")), Left(Refusal.NotADecider("mallory"))))
  }

  private def forged(files: ProjectFiles[IO]): IO[Unit] =
    val path = Records.path(TestsFile.format)
    files.read(path).map(_.flatMap(Wire.read(TestsFile.format, _).toOption).getOrElse(Map.empty))
      .map(_.view.mapValues((k, r) => (k, r.copy(outcome = Outcome.Passed))).toMap)
      .flatMap(t => files.writeIfChanged(path, Wire.print(TestsFile.format, t))).void

  private val dir = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-first")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  dir.test("the first deciders' list holds the developer's key under their name, sealed by it, written once") { d =>
    val key = d.resolve("signing.key")
    val env = Map("FRFLOW_KEY" -> key.toString)
    for
      _       <- IO.blocking(Files.writeString(key, throwaway))
      first   <- FrFlowApi.firstDecider[IO](d, "ann", env)
      again   <- FrFlowApi.firstDecider[IO](d, "bob", env)
      written <- IO.blocking(Files.readString(d.resolve(".frflow/deciders")))
      none    <- FrFlowApi.firstDecider[IO](d.resolve("elsewhere"), "ann", Map.empty).attempt
    yield
      val path = RelPath.fromIdentifiers(".frflow", "deciders")
      assertEquals((first, again), (Listed.Written(path), Listed.Already(path)))
      val list = Wire.read(DecidersFile.format, written).toOption
      assertEquals(list.map(_.entries.map(_.name)), Some(List("ann")))
      assert(list.flatMap(_.seal).isDefined, written)
      assert(none.isLeft, none)
  }

  /** A key made for this test only, in its own directory. */
  private def throwaway: String =
    val pair = KeyPairGenerator.getInstance("Ed25519").generateKeyPair()
    val b64 = Base64.getEncoder
    s"${b64.encodeToString(pair.getPrivate.getEncoded)}\n${b64.encodeToString(pair.getPublic.getEncoded)}\n"

