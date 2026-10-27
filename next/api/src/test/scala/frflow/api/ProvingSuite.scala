package frflow.api

import cats.syntax.all.*
import frflow.api.Opened.id
import frflow.api.node.lean.CheckState
import frflow.api.view.{CheckEvent, Scaffolded, Stop}
import frflow.core.name.RelPath

/** `Proving` over projects in memory, Lean scripted: the Lean written once; `status` writes the snapshot; a check
  * streams each level as it starts, then the view after it; without Lean, or of a node the model does not have, it
  * stops; `ci` checks everything; `scaffold` writes a proof file's stubs once.
  */
class ProvingSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))
  private val snapshot = RelPath.fromIdentifiers(".frflow", "kb.json")

  test("render writes the model's Lean: every module, then none while the model stays as it is") {
    Opened.api(Opened.before).flatMap(api => (api.proving.render, api.proving.render).tupled).map { (first, again) =>
      assert(first.exists(_.endsWith("nonNegative.Spec")), first)
      assertEquals(again, Nil)
    }
  }

  test("status writes the Lean and the snapshot, and gives the view") {
    for
      ports <- Opened.ports()
      view  <- Opened.over(Opened.before, ports).proving.status
      kb    <- ports.files.read(snapshot)
    yield
      assertEquals(view.nodes.map(_.id), List(nonNegative, sameAbove))
      assert(kb.exists(_.contains("nonNegative")), kb)
  }

  test("a check streams each level as it starts, parts first, then the view after it") {
    Opened.api(Opened.before).flatMap(api => Opened.events(api.proving.check(None))).map { events =>
      val levels = events.collect { case CheckEvent.Level(i, n, ids) => (i, n, ids) }
      assertEquals(levels, List((1, 2, List(sameAbove)), (2, 2, List(nonNegative))))
      events.lastOption match
        case Some(CheckEvent.Done(checked, after)) =>
          assertEquals(checked.toSet, Set(nonNegative, sameAbove))
          assertEquals(after.nodes.map(_.proof.state).distinct, List(CheckState.Proven))
          assert(after.node(sameAbove).flatMap(_.code).flatMap(_.tests).isDefined, after.node(sameAbove))
        case other => fail(s"the check did not end with its view: $other")
    }
  }

  test("a check of one node judges it alone; a check again finds the rest current") {
    for
      api   <- Opened.api(Opened.before)
      one   <- Opened.events(api.proving.check(Some(sameAbove)))
      again <- Opened.events(api.proving.check(None))
    yield
      assertEquals(one.collect { case CheckEvent.Level(_, _, ids) => ids }, List(List(sameAbove)))
      assertEquals(again.collect { case CheckEvent.Done(checked, _) => checked }, List(List(nonNegative)))
  }

  test("a check without Lean stops with NoLean; of a node the model does not have, with UnknownNode") {
    for
      absent  <- Opened.api(Opened.before, lean = Lean.Absent)
      api     <- Opened.api(Opened.before)
      noLean  <- Opened.events(absent.proving.check(None)).attempt
      unknown <- Opened.events(api.proving.check(Some(id("dragons")))).attempt
    yield assertEquals((noLean, unknown), (Left(Stop.NoLean), Left(Stop.UnknownNode(id("dragons")))))
  }

  test("ci checks everything, writes the snapshot, and ends with the view") {
    for
      ports  <- Opened.ports()
      events <- Opened.events(Opened.over(Opened.before, ports).proving.ci)
      kb     <- ports.files.read(snapshot)
    yield
      assert(kb.isDefined)
      assertEquals(events.collect { case CheckEvent.Done(_, v) => v.nodes.map(_.proof.state).distinct },
        List(List(CheckState.Proven)))
  }

  private val proofFile = RelPath.fromIdentifiers("lean", "Proofs/Shelf/nonNegative.lean")

  test("scaffold writes a proof file with a stub for complete before any check, then has nothing to add") {
    for
      ports   <- Opened.ports()
      api      = Opened.over(Opened.before, ports)
      first   <- api.proving.scaffold(nonNegative)
      text    <- ports.files.read(proofFile)
      again   <- api.proving.scaffold(nonNegative)
      unknown <- api.proving.scaffold(id("dragons")).attempt
      view    <- api.reading.view
    yield
      assertEquals(first, Scaffolded.Written(proofFile))
      assert(text.exists(t => t.contains("theorem complete : Obl.complete := by") &&
        t.contains("namespace Shelf.nonNegative.Proofs")), text)
      assertEquals((again, unknown), (Scaffolded.NothingToAdd, Left(Stop.UnknownNode(id("dragons")))))
      assertEquals(view.node(nonNegative).map(_.proof.authored), Some(true))
  }

  test("scaffold adds nothing to a proof file whose end it does not find, and says so") {
    for
      ports <- Opened.ports(Map(proofFile -> "import FrFlowGen.Shelf.nonNegative.Spec\n"))
      out   <- Opened.over(Opened.before, ports).proving.scaffold(nonNegative)
      text  <- ports.files.read(proofFile)
    yield assertEquals((out, text), (Scaffolded.EndNotFound(proofFile),
      Some("import FrFlowGen.Shelf.nonNegative.Spec\n")))
  }
