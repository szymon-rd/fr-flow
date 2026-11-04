package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Ledger, Payload, Uncounted}
import frflow.decision.review.ReviewState
import frflow.decision.rules.{Command, Refusal}
import frflow.project.{Projects, Tables}
import frflow.project.pipeline.Analysis
import frflow.project.port.{Records, RunCode}
import frflow.wire.file.Files
import frflow.wire.ledger.LedgerFile

/** `decide` on rooms in memory, with a key made for the run and listed as `ann`'s: refused to a name the key is not
  * listed under, before any rule; recorded, signed and counted for a decider; stored after the decisions the ledger
  * keeps that do not count; and `preview` records nothing.
  */
class DecideProgramSuite extends munit.CatsEffectSuite:
  private def first(a: Analysis): NodeId = a.subjects.inOrder.headOption.fold(fail("no subject"))(_.id)
  private def accept(a: Analysis) = Command.Accept(List(first(a)), "the booking form is trusted to send these", Nil,
    Map.empty)

  test("a key not listed under the name given is refused before any rule") {
    for
      p   <- Projects.inMemory(Map.empty)
      a   <- Projects.analysed(p, Projects.rooms, Nil)
      out <- DecideProgram(p.ports)(a.subjects, accept(a), "bob")
    yield assertEquals(out, Left(Refusal.NotADecider("bob")))
  }

  test("a decider's decision is signed by the key at hand, stored, and counts when the inputs are read again") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Nil)
      out    <- DecideProgram(p.ports)(a.subjects, accept(a), "ann")
      stored <- p.ports.ledger.load
      verify <- p.keys.verifier
      again  <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      val d = stored.current(first(a)).getOrElse(fail("not stored"))
      assertEquals(out.map(_.recorded.map(_._1)), Right(List(first(a))))
      assert(d.seal.exists(s => s.key == p.keys.id && verify(s, Payload.of(first(a), d))))
      assertEquals(again.reading.state(first(a)), ReviewState.Accepted)
  }

  test("taken over decisions that do not count, a decision is stored after them; they stay, still not counting") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Nil)
      seen   <- DecideProgram(p.ports).preview(a.subjects, accept(a), "ann")
      d       = seen.toOption.flatMap(_.recorded.headOption).getOrElse(fail("nothing previewed"))._2
      _      <- p.ports.ledger.update[String, Unit](l => Right((l.add(first(a), d), ())))
      second <- Projects.analysed(p, Projects.rooms, Nil)
      out    <- DecideProgram(p.ports)(second.subjects, accept(second), "ann")
      stored <- p.ports.ledger.load
      third  <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      assertEquals(second.inputs.ledger.others.map(x => (x._1, x._3)), List(first(a) -> Uncounted.NotListed))
      assert(out.isRight, out)
      assertEquals(stored.history(first(a)).map(_.seal.isDefined), List(false, true))
      assertEquals((third.inputs.ledger.counting.history(first(a)).size, third.inputs.ledger.others.size), (1, 1))
      assertEquals(third.reading.state(first(a)), ReviewState.Accepted)
  }

  test("every node of rooms is accepted one at a time, in the order decisions are taken, none waiting on another") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      tested <- TestProgram[IO](p.files, RunCode.inline[IO], Tables.sqlite(Projects.rooms))(a, None)
      ids     = tested._2.subjects.inOrder.map(_.id)
      out    <- ids.traverse(id => DecideProgram(p.ports)(tested._2.subjects,
                  Command.Accept(List(id), "it says what the service must do", Nil, Map.empty), "ann"))
      after  <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
    yield
      assertEquals(out.collect { case Left(r) => r }, Nil)
      assertEquals(ids.map(after.reading.state).distinct, List(ReviewState.Accepted))
  }

  test("preview says what a decision would record, and records nothing") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Nil)
      seen   <- DecideProgram(p.ports).preview(a.subjects, accept(a), "ann")
      stored <- p.ports.ledger.load
    yield
      assertEquals(seen.map(_.recorded.map((id, d) => (id, d.action))), Right(List(first(a) -> Action.Accept)))
      assertEquals(stored.decisions, Map.empty)
  }

  /** The ledger committed as it is now. */
  private def commit(p: Projects.InMemory): IO[Unit] =
    p.ports.ledger.load.flatMap(l => p.git.commit(Map(Records.path(LedgerFile.format) ->
      Files.print(LedgerFile.format, l)))).void

  private def dropLast(x: NodeId)(l: Ledger): Either[String, (Ledger, Unit)] =
    Right((Ledger(l.decisions.updated(x, l.history(x).init)), ()))

  test("a revisit committed, then taken out of the ledger: no decision is taken, and the node counts none") {
    for
      p       <- Projects.inMemory(Map.empty)
      a       <- Projects.analysed(p, Projects.rooms, Nil)
      (x, y)   = (first(a), a.subjects.inOrder(1).id)
      _       <- DecideProgram(p.ports)(a.subjects, accept(a), "ann")
      revisit <- DecideProgram(p.ports)(a.subjects, Command.Revisit(x, "the form may change"), "ann")
      _       <- commit(p)
      _       <- p.ports.ledger.update[String, Unit](dropLast(x))
      dropped <- Projects.analysed(p, Projects.rooms, Nil)
      out     <- DecideProgram(p.ports)(dropped.subjects, Command.Accept(List(y), "it is so", Nil, Map.empty), "ann")
      _       <- commit(p)
      read    <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      assert(revisit.isRight, revisit)
      assertEquals(out, Left(Refusal.Rewritten(List(x))))
      assertNotEquals(read.reading.state(x), ReviewState.Accepted)
      assertEquals(read.inputs.ledger.others.map(o => (o._1, o._3)).distinct, List(x -> Uncounted.Rewritten))
  }
