package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.example.Example
import frflow.core.name.{NodeId, RelPath}
import frflow.project.Projects
import frflow.project.check.{CheckProgram, Render}
import frflow.project.pipeline.Analysis
import frflow.project.port.RunCode
import frflow.project.port.{FrFlowError, Records}
import frflow.project.port.memory.ScriptedProver
import frflow.proof.layout.NodePart
import frflow.proof.prover.ast.ModuleName
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.RocqReport
import frflow.proof.rocq.RocqProject
import frflow.proof.verdict.*

/** `check` on rooms, Rocq scripted and the project in memory: nodes checked parts first and judged theorem by
  * theorem, each kept while current, the theory's own check recorded with its key; and each way a check ends early.
  */
class CheckProgramSuite extends munit.CatsEffectSuite:
  private def checked(only: Option[NodeId] = None)(say: Analysis => ModuleName => ProverRun)
      : IO[(List[NodeCheck], Analysis, ScriptedProver[IO], Projects.InMemory)] =
    checkedOf(Projects.rooms, Projects.roomsExamples, only)(say)

  private lazy val auth = Projects.elaborated(_root_.auth.knowledge)

  private def checkedOf(e: Elaborated, examples: List[Example], only: Option[NodeId])(
      say: Analysis => ModuleName => ProverRun)
      : IO[(List[NodeCheck], Analysis, ScriptedProver[IO], Projects.InMemory)] =
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, e, examples)
      lake <- ScriptedProver[IO](say(a), installed = true)
      out  <- CheckProgram(p.files, lake, RunCode.inline[IO])(a, only)
    yield (out._1, out._2, lake, p)

  private def proving(a: Analysis): ModuleName => ProverRun = Scripted(a, Set.empty, Set.empty).answer
  /** Rocq's report with no audit (`Print Assumptions`) in it. */
  private def unaudited(r: ProverRun): ProverRun = r match
    case ProverRun.Built(o)  => ProverRun.Built(o.linesIterator.filterNot(_.startsWith("assumes ")).mkString("\n"))
    case ProverRun.Failed(o) => ProverRun.Failed(o.linesIterator.filterNot(_.startsWith("assumes ")).mkString("\n"))
    case other               => other

  /** A report of one file Rocq did not read whole. */
  private def broken(file: String, why: String): String =
    RocqReport.print(List(RocqReport.File(file, Map.empty, Map.empty, Some(why))))

  private val stated = List("bookWhenFree", "acceptWhenFree", "neverOverlap", "storeWhenNoOverlap",
    "answerWhenNoOverlap").map(NodeId(_))

  test("every node Rocq is asked of is checked, parts first, proven when Rocq proves each obligation") {
    checked()(proving).map { (done, a, _, _) =>
      assertEquals(done.map(_.node).toSet, stated.toSet)
      assertEquals(done.filter(_.status != CheckStatus.Proven).map(c => c.node -> c.findings), Nil)
      val order = done.map(_.node)
      assert(order.indexOf(NodeId("storeWhenNoOverlap")) < order.indexOf(NodeId("bookWhenFree")), order)
      assert(order.indexOf(NodeId("answerWhenNoOverlap")) < order.indexOf(NodeId("acceptWhenFree")), order)
      assert(a.inputs.recorded.checks.whole.exists(_.key == a.keys.whole))
    }
  }

  test("a try Rocq does not prove shows nothing; the obligations there hold") {
    checked()(proving).map { (done, _, _, _) =>
      val book = done.find(_.node == NodeId("bookWhenFree")).getOrElse(fail("not checked"))
      assert(book.results.exists(_.name == ObligationName.Impl), book.results)
      assert(book.results.collect { case Result(ObligationName.Tried(_), s, _) => s }
        .forall(_ == ObligationStatus.NotShown), book.results)
    }
  }

  test("a second check builds nothing: every check is current; checks.json reads back as recorded") {
    for
      (_, a, lake, p) <- checked()(proving)
      before          <- lake.built
      again           <- CheckProgram(p.files, lake, RunCode.inline[IO])(a, None)
      after           <- lake.built
      read            <- Records.read(p.files)
    yield
      assertEquals((again._1, after.size), (Nil, before.size))
      assertEquals(read.checks, a.inputs.recorded.checks)
  }

  test("a model that does not build ends that node's check (ModelError); the nodes above wait for it") {
    val bad = NodeId("storeWhenNoOverlap")
    checked() { a => m =>
      if m == a.lowering.layout.ofNode(bad, NodePart.Spec) then ProverRun.Failed(
        broken("FrFlowGen/Rooms/storeWhenNoOverlap/Spec.v", "The reference x was not found."))
      else proving(a)(m)
    }.map { (done, _, _, _) =>
      val status = done.map(c => c.node -> c.status).toMap
      assertEquals(status(bad), CheckStatus.ModelError)
      assertEquals(status(NodeId("bookWhenFree")), CheckStatus.Waiting)
    }
  }

  test("a fatal try Rocq proves (a clash) fails the node, said as refuted") {
    checked()(a => Scripted(a, Set.empty, Set("clash")).answer).map { (done, _, _, _) =>
      val failed = done.filter(_.status == CheckStatus.Failed)
      assert(failed.nonEmpty && failed.forall(_.findings.contains(Finding.Refuted(List(TryKind.Clash)))), failed)
    }
  }

  test("a module Rocq did not run (one it imports did not go through) proves and shows nothing: the check is open") {
    val node = NodeId("storeWhenNoOverlap")
    checked(Some(node))(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Impl) then
      ProverRun.Failed(broken("FrFlowGen/Rooms/Types.v", "oops"))
      else proving(a)(m)).map { (done, _, _, _) =>
      val c = done.find(_.node == node).getOrElse(fail("not checked"))
      assertEquals(c.status, CheckStatus.Open)
      assert(c.results.exists(r => r.name == ObligationName.Impl && r.status == ObligationStatus.Unchecked),
        c.results)
      assert(c.results.collect { case Result(ObligationName.Tried(_), s, _) => s }.forall(_ ==
        ObligationStatus.NotShown), c.results)
    }
  }

  test("a proof whose audit Rocq did not print is not checked (fail closed): the node is open") {
    val node = NodeId("storeWhenNoOverlap")
    checked(Some(node))(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Impl) then
      unaudited(proving(a)(m)) else proving(a)(m)).map { (done, _, _, _) =>
      val c = done.find(_.node == node).getOrElse(fail("not checked"))
      assertEquals(c.status, CheckStatus.Open)
      assert(c.results.exists(r => r.name == ObligationName.Impl && r.status == ObligationStatus.Unchecked),
        c.results)
    }
  }

  test("a composition whose audit Rocq did not print does not prove the node") {
    val node = NodeId("accessNeedsGrant")
    checkedOf(auth, Nil, None)(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Theorems) then
      unaudited(proving(a)(m)) else proving(a)(m)).map { (done, _, _, _) =>
      assertEquals(done.find(_.node == node).map(c => (c.status, c.findings)),
        Some((CheckStatus.Open, List(Finding.NotProven(Nil)))))
    }
  }

  test("the theory's own check proves what Rocq audited, and nothing it did not") {
    val audited = checked()(proving)
    val not = checked()(a => m => if m == a.lowering.layout.whole then unaudited(proving(a)(m)) else proving(a)(m))
    (audited, not).mapN((yes, no) => List(yes, no).map(_._2.inputs.recorded.checks.whole.toList.flatMap(_.results)
      .map(_.status).filterNot(_ == ObligationStatus.NotShown).distinct)).map(statuses =>
      assertEquals(statuses, List(List(ObligationStatus.Proven), List(ObligationStatus.Unchecked))))
  }

  test("a .v file under rocq/Proofs/ that is no node's proof: the check is refused") {
    val stray = RelPath.fromIdentifiers("rocq", "Proofs/Rooms/sub/grantWhenFree.v")
    for
      p    <- Projects.inMemory(Map(stray -> "Lemma x : True.\nProof.\n  auto.\nQed.\n"))
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      lake <- ScriptedProver[IO](proving(a), installed = true)
      out  <- CheckProgram(p.files, lake, RunCode.inline[IO])(a, None).attempt
      held <- lake.built
    yield assertEquals((out.left.toOption, held), (Some(FrFlowError.StrayProofs(List(stray))), Nil))
  }

  test("a build that times out ends the check (Timeout); only that node is checked when it is named") {
    val node = NodeId("answerWhenNoOverlap")
    checked(Some(node))(a => m => if m.dotted.contains(".answerWhenNoOverlap.") then ProverRun.TimedOut("") else
      proving(a)(m)).map { (done, _, _, _) =>
      assertEquals(done.map(c => c.node -> c.status), List(node -> CheckStatus.Timeout))
    }
  }

  test("no Rocq: the check is refused; a node the model does not have, too") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      none <- ScriptedProver[IO](_ => ProverRun.Built(""), installed = false)
      lake <- ScriptedProver[IO](_ => ProverRun.Built(""), installed = true)
      no   <- CheckProgram(p.files, none, RunCode.inline[IO])(a, None).attempt
      gone <- CheckProgram(p.files, lake, RunCode.inline[IO])(a, Some(NodeId("gone"))).attempt
    yield
      assertEquals(no.left.toOption, Some(FrFlowError.NoProver))
      assertEquals(gone.left.toOption, Some(FrFlowError.UnknownNode(NodeId("gone"))))
  }

  test("the Rocq written: where an editor finds what is compiled, every module; a module the model no longer has is " +
    "deleted") {
    val stale = RelPath.fromIdentifiers("rocq", "FrFlowGen/Rooms/gone/Spec.v")
    for
      p    <- Projects.inMemory(Map(stale -> "(* gone *)"))
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      _    <- Render(p.files)(a)
      held <- p.files.all
    yield
      assert(!held.contains(stale))
      assert(held.get(Render.project).exists(_.contains("-Q _build/FrFlowGen FrFlowGen")))
      assertEquals(a.rocq.unprinted, Map.empty[String, String])
      assert(a.modules.forall(m => held.contains(RocqProject.path(m.name))))
  }
