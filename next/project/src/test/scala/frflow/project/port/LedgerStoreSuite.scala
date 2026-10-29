package frflow.project.port

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Content, FieldValue}
import frflow.decision.ledger.*
import frflow.project.Live
import frflow.project.port.memory.MemoryLedger
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import java.time.Instant

/** The laws of the ledger's store, on each interpreter: an update stores what it returns only on `Right`, and a
  * load then gives it; updates at once are serialized, each on the ledger the one before stored. The file is
  * written as UTF-8, and a file that does not read is said, never taken as empty.
  */
class LedgerStoreSuite extends munit.CatsEffectSuite:
  private def decision(i: Int) = Decision.taken(Action.Accept, Authorship("dév", Instant.ofEpochSecond(i), None),
    Reason(s"accepted, round $i", Nil), Bound(Content(List("statement" -> FieldValue.Text("∀ réservation"))),
      Chain.empty, None))
  private val root = NodeId("Root")
  private def added(l: Ledger): Either[String, (Ledger, Int)] = Right((l.add(root, decision(l.history(root).size)),
    l.history(root).size))

  private def laws(name: String, store: Resource[IO, LedgerStore[IO]], tags: Set[munit.Tag]): Unit =
    test(munit.TestOptions(s"$name: an update stores only on Right, and a load gives what it stored").withTags(tags)) {
      store.use(s =>
        for
          refused <- s.update[String, Int](_ => Left("no"))
          empty   <- s.load
          done    <- s.update(added)
          loaded  <- s.load
        yield assertEquals((refused, empty, done, loaded.history(root).size), (Left("no"), Ledger.empty, Right(0), 1)))
    }

    test(munit.TestOptions(s"$name: updates at once are serialized, each on the one before").withTags(tags)) {
      store.use(s => (1 to 12).toList.parTraverse(_ => s.update(added)) >> s.load).map(l =>
        assertEquals(l.history(root).map(_.reason.text), (0 until 12).map(i => s"accepted, round $i").toList))
    }

  laws("memory", Resource.eval(MemoryLedger[IO](Ledger.empty)).widen, Set.empty)
  laws("file", Resource.make(IO(Files.createTempDirectory("frflow-ledger")))(d => IO.blocking(Files.walk(d)
    .sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))).flatMap(LedgerStore.file[IO]),
    Set(Live))

  test("the file is UTF-8; a ledger that does not read is raised, not taken as empty".tag(Live)) {
    for
      dir   <- IO(Files.createTempDirectory("frflow-ledger"))
      _     <- LedgerStore.file[IO](dir).use(_.update(added))
      bytes  = Files.readAllBytes(dir.resolve(".frflow/ledger.json"))
      _     <- IO(Files.writeString(dir.resolve(".frflow/ledger.json"), "{ not json"))
      bad   <- LedgerStore.file[IO](dir).use(_.load).attempt
    yield
      assert(String(bytes, UTF_8).contains("∀ réservation"))
      assert(bad.left.exists { case FrFlowError.NotRead(_) => true; case _ => false }, bad)
  }
