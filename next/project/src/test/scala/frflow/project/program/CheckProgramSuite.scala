package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.name.{NodeId, RelPath}
import frflow.project.Projects
import frflow.project.check.{CheckProgram, Render}
import frflow.project.pipeline.Analysis
import frflow.project.port.RunCode
import frflow.project.port.{FrFlowError, Records}
import frflow.project.port.memory.ScriptedLake
import frflow.proof.layout.NodePart
import frflow.proof.lean.ast.ModuleName
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.verdict.*

/** `check` on rooms, Lean scripted and the project in memory: nodes checked parts first and judged theorem by
  * theorem, each kept while current, the theory's own check recorded with its key; and each way a check ends early.
  */
class CheckProgramSuite extends munit.CatsEffectSuite:
  private val library = "../../../next/proof/lean"

  private def checked(only: Option[NodeId] = None)(say: Analysis => ModuleName => ProverRun)
      : IO[(List[NodeCheck], Analysis, ScriptedLake[IO], Projects.InMemory)] =
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      lake <- ScriptedLake[IO](say(a), installed = true)
      out  <- CheckProgram(p.files, lake, library, RunCode.inline[IO])(a, only)
    yield (out._1, out._2, lake, p)

  private def proving(a: Analysis): ModuleName => ProverRun = Scripted(a, Set.empty, Set.empty).answer
  /** Lean's output with no audit (`#print axioms`) in it. */
  private def unaudited(r: ProverRun): ProverRun = r match
    case ProverRun.Built(o)  => ProverRun.Built(o.linesIterator.filterNot(_.contains("axioms")).mkString("\n"))
    case ProverRun.Failed(o) => ProverRun.Failed(o.linesIterator.filterNot(_.contains("axioms")).mkString("\n"))
    case other               => other

  private val stated = List("bookWhenFree", "answerWhenFree", "endsAfterStart", "neverOverlap", "bookingsOfTheRoom",
    "roomBookingsApart", "grantWhenFree", "grantWhenNoOverlap", "requestsEndAfterStart").map(NodeId(_))

  test("every node Lean is asked of is checked, parts first, proven when Lean proves each obligation") {
    checked()(proving).map { (done, a, _, _) =>
      assertEquals(done.map(_.node).toSet, stated.toSet)
      assertEquals(done.filter(_.status != CheckStatus.Proven).map(c => c.node -> c.findings), Nil)
      val order = done.map(_.node)
      assert(order.indexOf(NodeId("grantWhenNoOverlap")) < order.indexOf(NodeId("grantWhenFree")), order)
      assert(order.indexOf(NodeId("grantWhenFree")) < order.indexOf(NodeId("bookWhenFree")), order)
      assert(a.inputs.recorded.checks.whole.exists(_.key == a.keys.whole))
    }
  }

  test("a try Lean does not prove is an error in the checks module and shows nothing; the obligations there hold") {
    checked()(proving).map { (done, _, _, _) =>
      val book = done.find(_.node == NodeId("grantWhenFree")).getOrElse(fail("not checked"))
      assert(book.results.exists(_.name == ObligationName.Complete), book.results)
      assert(book.results.collect { case Result(ObligationName.Tried(_), s, _) => s }
        .forall(_ == ObligationStatus.NotShown), book.results)
    }
  }

  test("a second check builds nothing: every check is current; checks.json reads back as recorded") {
    for
      (_, a, lake, p) <- checked()(proving)
      before          <- lake.built
      again           <- CheckProgram(p.files, lake, library, RunCode.inline[IO])(a, None)
      after           <- lake.built
      read            <- Records.read(p.files)
    yield
      assertEquals((again._1, after.size), (Nil, before.size))
      assertEquals(read.checks, a.inputs.recorded.checks)
  }

  test("a model that does not build ends that node's check (ModelError); the nodes above wait for it") {
    val bad = NodeId("grantWhenNoOverlap")
    checked() { a => m =>
      if m == a.lowering.layout.ofNode(bad, NodePart.Spec) then ProverRun.Failed(
        "error: FrFlowGen/Rooms/grantWhenNoOverlap/Spec.lean:3:0: unknown identifier")
      else proving(a)(m)
    }.map { (done, _, _, _) =>
      val status = done.map(c => c.node -> c.status).toMap
      assertEquals(status(bad), CheckStatus.ModelError)
      assertEquals(status(NodeId("grantWhenFree")), CheckStatus.Waiting)
    }
  }

  test("a fatal try Lean proves (a clash) fails the node, said as refuted") {
    checked()(a => Scripted(a, Set.empty, Set("clash")).answer).map { (done, _, _, _) =>
      val failed = done.filter(_.status == CheckStatus.Failed)
      assert(failed.nonEmpty && failed.forall(_.findings.contains(Finding.Refuted(List(TryKind.Clash)))), failed)
    }
  }

  test("a module Lake did not run (one it imports failed) proves nothing and shows nothing: the check is open") {
    val node = NodeId("neverOverlap")
    checked(Some(node))(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Checks) then
      ProverRun.Failed("✖ [2/3] Building FrFlowGen.Rooms.Types\nerror: FrFlowGen/Rooms/Types.lean:1:0: oops")
      else proving(a)(m)).map { (done, _, _, _) =>
      val c = done.find(_.node == node).getOrElse(fail("not checked"))
      assertEquals(c.status, CheckStatus.Open)
      assert(c.results.exists(r => r.name == ObligationName.Cover("book") && r.status == ObligationStatus.Unchecked),
        c.results)
      assert(c.results.collect { case Result(ObligationName.Tried(_), s, _) => s }.forall(_ ==
        ObligationStatus.NotShown), c.results)
    }
  }

  test("a proof whose audit Lean did not print is not checked (fail closed): the node is open") {
    val node = NodeId("neverOverlap")
    checked(Some(node))(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Checks) then
      unaudited(proving(a)(m)) else proving(a)(m)).map { (done, _, _, _) =>
      val c = done.find(_.node == node).getOrElse(fail("not checked"))
      assertEquals(c.status, CheckStatus.Open)
      assert(c.results.exists(r => r.name == ObligationName.Cover("book") && r.status == ObligationStatus.Unchecked),
        c.results)
    }
  }

  test("a composition whose audit Lean did not print does not prove the node") {
    val node = NodeId("grantWhenFree")
    checked(Some(node))(a => m => if m == a.lowering.layout.ofNode(node, NodePart.Theorems) then
      unaudited(proving(a)(m)) else proving(a)(m)).map { (done, _, _, _) =>
      assertEquals(done.find(_.node == node).map(c => (c.status, c.findings)),
        Some((CheckStatus.Open, List(Finding.NotProven(Nil)))))
    }
  }

  test("the theory's own check proves what Lean audited, and nothing it did not") {
    val audited = checked()(proving)
    val not = checked()(a => m => if m == a.lowering.layout.whole then unaudited(proving(a)(m)) else proving(a)(m))
    (audited, not).mapN((yes, no) => List(yes, no).map(_._2.inputs.recorded.checks.whole.toList.flatMap(_.results)
      .map(_.status).filterNot(_ == ObligationStatus.NotShown).distinct)).map(statuses =>
      assertEquals(statuses, List(List(ObligationStatus.Proven), List(ObligationStatus.Unchecked))))
  }

  test("a .lean file under lean/Proofs/ that is no node's proof: the check is refused") {
    val stray = RelPath.fromIdentifiers("lean", "Proofs/Rooms/sub/grantWhenFree.lean")
    for
      p    <- Projects.inMemory(Map(stray -> "theorem x : True := trivial"))
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      lake <- ScriptedLake[IO](proving(a), installed = true)
      out  <- CheckProgram(p.files, lake, library, RunCode.inline[IO])(a, None).attempt
      held <- lake.built
    yield assertEquals((out.left.toOption, held), (Some(FrFlowError.StrayProofs(List(stray))), Nil))
  }

  test("a build that times out ends the check (Timeout); only that node is checked when it is named") {
    val node = NodeId("endsAfterStart")
    checked(Some(node))(a => m => if m.dotted.contains(".endsAfterStart.") then ProverRun.TimedOut("") else
      proving(a)(m)).map { (done, _, _, _) =>
      assertEquals(done.map(c => c.node -> c.status), List(node -> CheckStatus.Timeout))
    }
  }

  test("no Lean: the check is refused; a node the model does not have, too") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      none <- ScriptedLake[IO](_ => ProverRun.Built(""), installed = false)
      lake <- ScriptedLake[IO](_ => ProverRun.Built(""), installed = true)
      no   <- CheckProgram(p.files, none, library, RunCode.inline[IO])(a, None).attempt
      gone <- CheckProgram(p.files, lake, library, RunCode.inline[IO])(a, Some(NodeId("gone"))).attempt
    yield
      assertEquals(no.left.toOption, Some(FrFlowError.NoLean))
      assertEquals(gone.left.toOption, Some(FrFlowError.UnknownNode(NodeId("gone"))))
  }

  test("the Lean written: the lakefile, the toolchain, every module; a module the model no longer has is deleted") {
    val stale = RelPath.fromIdentifiers("lean", "FrFlowGen/Rooms/gone/Spec.lean")
    for
      p    <- Projects.inMemory(Map(stale -> "-- gone"))
      a    <- Projects.analysed(p, Projects.rooms, Nil)
      _    <- Render(p.files, library)(a)
      held <- p.files.all
    yield
      assert(!held.contains(stale))
      assert(held.get(Render.lakefile).exists(_.contains(s"path = \"$library\"")))
      assert(a.modules.forall(m => held.contains(m.name.file)))
  }
