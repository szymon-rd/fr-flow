package frflow
package ledger

import cats.effect.IO
import cats.syntax.all.*
import frflow.protocol.*
import java.nio.file.{Files, Path}
import java.time.Instant

/** The files the ledger module keeps, in temporary directories: the ledger, and the requests. */
class StoresSuite extends munit.CatsEffectSuite:

  private val now = Instant.parse("2026-01-01T00:00:00Z")
  private def file(name: String): IO[Path] = IO.blocking(Files.createTempDirectory("frflow-store").resolve(s".frflow/$name"))
  private def decision(reason: String) = Decision(Action.Accept, "dev", Instant.parse("2026-01-01T00:00:00Z"), reason, chain = Chain("c"))

  test("the ledger survives its file; a file that does not read is an error, not an empty ledger") {
    for
      f     <- file("ledger.json")
      store <- JsonStore.make(f, Ledger.empty)
      empty <- store.load
      l      = Ledger.empty.add(NodeId("Root"), decision("it is the idea"))
      _     <- store.update(_ => Right(l -> ()))
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
      store   <- JsonStore.make(f, Ledger.empty)
      refused <- store.update[Refusal, Unit](_ => Left(Refusal.NoReason))
      exists  <- IO.blocking(Files.exists(f))
      _       <- (1 to 20).toList.parTraverse_(i =>
                   store.update[Refusal, Unit](l => Right(l.add(NodeId(s"N$i"), decision(s"reason number $i")) -> ())))
      after   <- store.load
    yield
      assertEquals(refused, Left(Refusal.NoReason))
      assert(!exists)
      assertEquals(after.decisions.size, 20)
  }

  test("requests are asked, answered and closed in their file") {
    for
      f        <- file("requests.json")
      store    <- JsonStore.make(f, List.empty[Request])
      none     <- store.load
      asked    <- store.update[Refusal, Request](rs => Right(Requests.ask(rs, Some(NodeId("Pick")), "Pick faster.", "dev", now)))
      answered <- store.update(Requests.answer(_, "Pick", "Picking is now quicker.", _ => false, now))
      unknown  <- store.update(Requests.answer(_, "Nowhere", "text", _ => false, now))
      closed   <- store.update(Requests.close(_, asked.toOption.map(_.id).toList))
      all      <- store.load
    yield
      assertEquals(none, Nil)
      assertEquals(answered.map(r => (r.id, r.answer)), asked.map(a => (a.id, Some("Picking is now quicker."))))
      assertEquals(unknown, Left(Refusal.UnknownRequest("Nowhere")))
      assertEquals(closed.map(_.map(_.status)), Right(List(RequestStatus.Closed)))
      assertEquals(all.map(r => (r.status, r.answer)), List((RequestStatus.Closed, Some("Picking is now quicker."))))
  }
