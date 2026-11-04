package frflow.api

import cats.syntax.all.*
import frflow.api.fixture.{Assembled, Opened, Shelf}
import frflow.api.fixture.Opened.id
import frflow.api.node.lean.CheckState
import frflow.api.node.Relation
import frflow.api.view.Warning
import frflow.core.name.RelPath
import frflow.core.spec.NodeKind
import frflow.decision.review.ReviewState
import frflow.project.Projects

/** `Reading` over projects in memory: the view (each node by concept, in decision order, with the roots and the
  * overview), a node's diff, and the model's fingerprint. Where a change belongs is `ReportsSuite`'s.
  */
class ReadingSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))

  test("the view holds each node in decision order, the roots, and the overview of where they stand") {
    Opened.api(Opened.before).flatMap(_.reading.view).map { v =>
      assertEquals(v.nodes.map(_.id), List(nonNegative, sameAbove))
      assertEquals(v.roots, List(nonNegative))
      assertEquals((v.overview.review(ReviewState.Proposed), v.overview.checks(CheckState.Unchecked)), (2, 2))
      assertEquals((v.overview.complete, v.gone), (false, Nil))
    }
  }

  test("a node's view: what it says, where it sits, what is shown of it, and where the developer stands") {
    Opened.api(Opened.before).flatMap(_.reading.view).map { v =>
      val n = v.node(sameAbove).getOrElse(fail("no node"))
      assertEquals(n.says.kind, NodeKind.Claim)
      assertEquals(n.says.statement, "Above zero, the service gives the number itself.")
      assert(n.says.checking.nonEmpty && n.says.reason.isEmpty, n.says)
      assertEquals((n.place(Relation.Parent), n.place.root), (List(nonNegative), false))
      assertEquals(v.node(nonNegative).map(_.place(Relation.Part)), Some(List(sameAbove)))
      assertEquals((n.proof.state, n.proof.results, n.proof.authored), (CheckState.Unchecked, Nil, false))
      assert(n.code.exists(c => c.shown.tested.nonEmpty && c.tests.isEmpty), n.code)
      assertEquals((n.review.standing.state, n.review.decisions.binding, n.review.moves.above),
        (ReviewState.Proposed, None, Nil))
    }
  }

  test("a node's diff: nothing moved before its decision; none for a node the model does not have") {
    Opened.api(Opened.before).flatMap(api => (api.reading.diff(sameAbove), api.reading.diff(id("gone"))).tupled)
      .map { (d, none) =>
        assertEquals(d.map(x => (x.fields, x.above, x.parts.added, x.code)), Some((Nil, Nil, Nil, None)))
        assertEquals(none, None)
      }
  }

  test("the view warns of a design governing nothing there, code nothing governs (whatever its text), a proof " +
    "file of no node, and a deciders' list not committed") {
    val (other, gone) = (RelPath.fromIdentifiers("src/main", "Other.scala"),
      RelPath.fromIdentifiers("lean", "Proofs/Governed/gone.lean"))
    val files = Map(other -> "// FrModel(\"Other\") is not here", gone -> "",
      RelPath.fromIdentifiers(".frflow", "deciders") -> "{}")
    Opened.ports(files).flatMap(p => Opened.over(Opened.project(Shelf.Governed.kb), p).flatMap(_.reading.view))
      .map { v =>
      assertEquals(v.warnings.collect {
        case w @ (_: Warning.GovernedMissing | _: Warning.Ungoverned | _: Warning.ProofFileOfNoNode) => w
        case Warning.DecidersUncommitted => Warning.DecidersUncommitted
      }, List(Warning.DecidersUncommitted, Warning.Ungoverned(other),
        Warning.GovernedMissing(RelPath.fromIdentifiers("src/main", "shelf"), id("inShelf")),
        Warning.ProofFileOfNoNode(gone)))
    }
  }

  test("the file a FrModel is assembled in is the model's own, not code nothing governs") {
    val e = Projects.elaborated(Assembled.kb)
    val assembled = e.theory.writtenIn.getOrElse(fail("no file recorded"))
    assert(!e.theory.nodes.exists(_.at.file == assembled), assembled)
    Opened.ports(Map(assembled -> "object Assembled")).flatMap(p => Opened.over(Opened.project(Assembled.kb), p)
      .flatMap(_.reading.view)).map(v => assertEquals(v.warnings.collect { case w: Warning.Ungoverned => w }, Nil))
  }

  test("the model's fingerprint moves when a source file does, and only then") {
    val file = RelPath.fromIdentifiers("src/main", "Calendar.scala")
    for
      ports <- Opened.ports(Map(file -> "object Calendar"))
      api   <- Opened.over(Opened.before, ports)
      first <- api.reading.modelFingerprint
      again <- api.reading.modelFingerprint
      _     <- ports.files.writeIfChanged(file, "object Calendar { val rooms = 2 }")
      moved <- api.reading.modelFingerprint
    yield assertEquals((first == again, first == moved), (true, false))
  }

  test("status warns of a schedule over a model no program writes (the 13d re-review's R-N1), not of one written") {
    List(frflow.eval.time.Unwritten.model, frflow.eval.time.Lapse.lapse).traverse(m =>
      Opened.api(Opened.project(m)).flatMap(_.reading.view).map(_.warnings.collect {
        case w: Warning.ScheduleUnwritten => w
      })).map(ws => assertEquals(ws, List(List(Warning.ScheduleUnwritten(id("stale"),
        List(frflow.core.name.ModelName("housekept")))), Nil)))
  }

  test("status warns of an assumption the generated runs cannot evaluate: trusted, not tested") {
    Opened.api(Opened.project(frflow.eval.assumed.Lookup.alike)).flatMap(_.reading.view).map(v =>
      assertEquals(v.warnings.collect { case w: Warning.TrustedUntested => w },
        List(Warning.TrustedUntested(id("hasAlike"), List(frflow.core.name.SymbolName("has"))))))
  }
