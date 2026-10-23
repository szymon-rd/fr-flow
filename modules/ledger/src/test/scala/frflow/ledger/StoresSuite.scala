package frflow
package ledger

import cats.effect.IO
import cats.syntax.all.*
import frflow.protocol.*
import java.nio.file.{Files, Path}

/** The files the ledger module keeps, in temporary directories: the ledger, and the requests. */
class StoresSuite extends munit.CatsEffectSuite:

  private def file(name: String): IO[Path] = IO.blocking(Files.createTempDirectory("frflow-store").resolve(s".frflow/$name"))
  private def decision(reason: String) = Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", reason, chain = Chain("c"))

  test("the ledger survives its file; a file that does not read is an error, not an empty ledger") {
    for
      f     <- file("ledger.json")
      store <- LedgerStore.make(f)
      empty <- store.load
      l      = Ledger.empty.add(NodeId("Root"), decision("it is the idea"))
      _     <- store.save(l)
      back  <- store.load
      _     <- IO.blocking(Files.writeString(f, "{ not json"))
      bad   <- store.load.attempt
    yield
      assertEquals(empty, Ledger.empty)
      assertEquals(back, l)
      assert(bad.left.exists(_.isInstanceOf[LedgerError.BadFile]), bad)
  }

  test("an update refused writes nothing; concurrent updates each see the one before") {
    for
      f       <- file("ledger.json")
      store   <- LedgerStore.make(f)
      refused <- store.update(_ => Left(Refusal.NoReason))
      exists  <- IO.blocking(Files.exists(f))
      _       <- (1 to 20).toList.parTraverse_(i =>
                   store.update(l => Right(l.add(NodeId(s"N$i"), decision(s"reason number $i")) -> ())))
      after   <- store.load
    yield
      assertEquals(refused, Left(Refusal.NoReason))
      assert(!exists)
      assertEquals(after.decisions.size, 20)
  }

  test("requests are asked, answered and closed in their file") {
    for
      f        <- file("requests.json")
      store    <- RequestStore.make(f)
      none     <- store.load
      asked    <- store.ask(Some(NodeId("Pick")), "Pick faster.", "dev")
      answered <- store.answer("Pick", "Picking is now quicker.", _ => false)
      unknown  <- store.answer("Nowhere", "text", _ => false)
      closed   <- store.close(asked.id)
      all      <- store.load
    yield
      assertEquals(none, Nil)
      assertEquals(answered.map(r => (r.id, r.answer)), Right((asked.id, Some("Picking is now quicker."))))
      assertEquals(unknown, Left(Refusal.UnknownRequest("Nowhere")))
      assertEquals(closed.map(_.status), Right(RequestStatus.Closed))
      assertEquals(all.map(r => (r.status, r.answer)), List((RequestStatus.Closed, Some("Picking is now quicker."))))
  }
