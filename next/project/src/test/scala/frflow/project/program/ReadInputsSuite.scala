package frflow.project.program

import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Reason, Uncounted}
import frflow.decision.review.ReviewState
import frflow.decision.rules.{Command, Refusal}
import frflow.project.Projects
import frflow.project.port.Records
import frflow.project.report.Review
import frflow.wire.file.Files
import frflow.wire.ledger.LedgerFile

/** The inputs a run reads: the ledger as it counts, against the committed deciders' list and the ledger as
  * committed: a node whose committed history is not where its history now starts (its last decision taken out of
  * the file) counts none of its decisions, which are said, each with why.
  */
class ReadInputsSuite extends munit.CatsEffectSuite:
  test("a decision taken out of the ledger since the commit: the node counts none of its decisions") {
    for
      p         <- Projects.inMemory(Map.empty)
      a         <- Projects.analysed(p, Projects.rooms, Nil)
      id         = a.subjects.inOrder.headOption.fold(fail("no subject"))(_.id)
      _         <- DecideProgram(p.ports)(a.subjects, Command.Accept(List(id), "it says what is trusted", Nil,
                     Map.empty), "ann")
      working   <- p.ports.ledger.load
      committed  = working.add(id, working.current(id).fold(fail("none"))(_.copy(reason = Reason("revised", Nil))))
      _         <- p.git.commit(Map(Records.path(LedgerFile.format) -> Files.print(LedgerFile.format, committed)))
      read      <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      assertEquals(read.inputs.ledger.others.map(x => (x._1, x._3)), List(id -> Uncounted.Rewritten))
      assertEquals(read.reading.state(id), ReviewState.Proposed)
  }

  test("with the committed ledger where the working one starts, every decision a decider signed counts") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      id    = a.subjects.inOrder.headOption.fold(fail("no subject"))(_.id)
      _    <- p.git.commit(Map(Records.path(LedgerFile.format) -> Files.print(LedgerFile.format,
                frflow.decision.ledger.Ledger.empty)))
      _    <- DecideProgram(p.ports)(a.subjects, Command.Accept(List(id), "it says what is trusted", Nil, Map.empty),
                "ann")
      read <- Projects.analysed(p, Projects.rooms, Nil)
    yield assertEquals((read.inputs.ledger.others, read.reading.state(id)), (Nil, ReviewState.Accepted))
  }

  test("a committed version of the ledger that does not read: no decision counts, and none is taken") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      id    = a.subjects.inOrder.headOption.fold(fail("no subject"))(_.id)
      _    <- DecideProgram(p.ports)(a.subjects, Command.Accept(List(id), "it says what is trusted", Nil, Map.empty),
                "ann")
      _    <- p.git.commit(Map(Records.path(LedgerFile.format) -> "{ not a ledger"))
      read <- Projects.analysed(p, Projects.rooms, Nil)
      out  <- DecideProgram(p.ports)(read.subjects, Command.Accept(List(id), "again", Nil, Map.empty), "ann")
    yield
      assertEquals(read.inputs.ledger.others.map(x => (x._1, x._3)), List(id -> Uncounted.Unreadable))
      assertEquals(read.reading.state(id), ReviewState.Proposed)
      assertEquals(out, Left(Refusal.Rewritten(List(id))))
  }

  test("a proof is lean/Proofs/<Model>/<Node>.lean, directly there and named by an identifier; any other a stray") {
    def at(path: String) = RelPath.fromIdentifiers("lean", s"Proofs/$path")
    val strays = List(at("Rooms/sub/grantWhenFree.lean"), at("Rooms/not-a-node.lean"), at("Other/grantWhenFree.lean"),
      at("Stray.lean"))
    for
      p <- Projects.inMemory((at("Rooms/grantWhenFree.lean") :: strays).map(_ -> "theorem x : True := trivial").toMap)
      a <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      assertEquals(a.inputs.lean.proofs.keySet, Set(NodeId("grantWhenFree")))
      assertEquals(a.inputs.lean.strays.toSet, strays.toSet)
      assertEquals(Review.of(a).strays.toSet, strays.toSet)
  }
