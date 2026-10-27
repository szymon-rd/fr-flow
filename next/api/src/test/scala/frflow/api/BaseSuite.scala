package frflow.api

import cats.effect.IO
import frflow.api.Opened.id
import frflow.api.view.Warning
import frflow.core.name.RelPath
import frflow.decision.ledger.Ledger
import frflow.decision.rules.{Command, Refusal}
import frflow.project.Projects
import frflow.project.port.Records
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.LedgerFile

/** The ledger's base (`rebase`): a committed deletion locks deciding until a listed decider rebases and the base is
  * committed with the ledger it names; the base is anchored to that commit, so a ledger text committed again later
  * rewrites what was decided since, and is refused; with nothing rewritten there is nothing to rebase; a base not
  * committed with its ledger is warned of.
  */
class BaseSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))
  private val ledger = Records.path(LedgerFile.format)
  private val base = RelPath.fromIdentifiers(".frflow", "ledger-base")
  private val revisit = Command.Revisit(sameAbove, "the shelf may hold more")
  private def text(l: Ledger) = Wire.print(LedgerFile.format, l)
  private def locked[A](r: Either[Refusal, A]) = r match
    case Left(Refusal.Rewritten(_)) => true
    case _                          => false

  /** Every node accepted and committed, then the deletion of every decision committed (its text
    * ending as `end` says: a blank line at its end, as a merge may leave it).
    */
  private def deleted: IO[(Projects.InMemory, FrFlowApi[IO])] = deletedAs("")

  private def deletedAs(end: String): IO[(Projects.InMemory, FrFlowApi[IO])] =
    for
      p   <- Projects.inMemory(Map.empty)
      api <- Opened.over(Opened.before, p.ports)
      _   <- Opened.acceptAll(api)
      _   <- p.ports.ledger.load.flatMap(l => p.git.commit(Map(ledger -> text(l))))
      _   <- p.ports.ledger.update(_ => Right((Ledger.empty, ())))
      _   <- p.git.commit(Map(ledger -> (text(Ledger.empty) + end)))
    yield (p, api)

  /** The ledger as rebase wrote it, committed with the base. */
  private def committed(p: Projects.InMemory): IO[String] =
    for
      now  <- p.ports.ledger.load.map(text)
      file <- p.files.read(base)
      _    <- p.git.commit(Map(ledger -> now) ++ file.map(base -> _))
    yield now

  test("a committed deletion locks deciding until a decider rebases and both files are committed") {
    for
      (p, api) <- deleted
      locked1  <- api.deciding.decide(revisit, "ann")
      other    <- api.deciding.rebase("bob")
      based    <- api.deciding.rebase("ann")
      pending  <- api.reading.view.map(_.warnings)
      _        <- committed(p)
      again    <- Opened.acceptAll(api) >> api.deciding.decide(revisit, "ann")
      warned   <- api.reading.view.map(_.warnings)
    yield
      assert(locked(locked1), locked1)
      assertEquals(other, Left(Refusal.NotADecider("bob")))
      assertEquals(based.map(_.file), Right(base))
      assert(pending.contains(Warning.BaseNotCommitted), pending)
      assert(again.isRight, again)
      assert(!warned.contains(Warning.BaseNotCommitted), warned)
  }

  test("after a rebase, the base's ledger text committed again does not erase what was decided since") {
    for
      (p, api) <- deleted
      _        <- api.deciding.rebase("ann")
      at       <- committed(p)
      _        <- Opened.acceptAll(api)
      _        <- p.ports.ledger.load.flatMap(l => p.git.commit(Map(ledger -> text(l))))
      _        <- api.deciding.decide(revisit, "ann")
      _        <- p.ports.ledger.load.flatMap(l => p.git.commit(Map(ledger -> text(l))))
      _        <- p.ports.ledger.update(_ => Right((Wire.read(LedgerFile.format, at).getOrElse(Ledger.empty), ())))
      _        <- p.git.commit(Map(ledger -> at))
      out      <- api.deciding.decide(Command.Revisit(nonNegative, "is deciding still locked here"), "ann")
    yield assert(locked(out), out)
  }

  test("with nothing rewritten there is nothing to rebase") {
    for
      p   <- Projects.inMemory(Map.empty)
      api <- Opened.over(Opened.before, p.ports)
      _   <- Opened.acceptAll(api)
      _   <- p.ports.ledger.load.flatMap(l => p.git.commit(Map(ledger -> text(l))))
      out <- api.deciding.rebase("ann")
    yield assertEquals(out, Left(Refusal.NothingToRebase))
  }

  test("a base committed without the ledger text it names is warned of, and does not take") {
    for
      (p, api) <- deletedAs("\n")
      _        <- api.deciding.rebase("ann")
      file     <- p.files.read(base)
      _        <- p.git.commit(file.map(base -> _).toMap)
      warned   <- api.reading.view.map(_.warnings)
      out      <- api.deciding.decide(revisit, "ann")
    yield
      assert(warned.contains(Warning.BaseNotCommitted), warned)
      assert(locked(out), out)
  }
