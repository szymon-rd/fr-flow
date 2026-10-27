package frflow.project.program

import frflow.decision.ledger.{Reason, Uncounted}
import frflow.decision.review.ReviewState
import frflow.decision.rules.Command
import frflow.project.Projects
import frflow.project.port.Records
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
