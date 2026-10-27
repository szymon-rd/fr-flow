package frflow.project

import cats.effect.{IO, Resource}
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.NodeKind
import frflow.decision.ledger.Ledger
import frflow.project.check.CheckProgram
import frflow.project.pipeline.Analysis
import frflow.project.port.*
import frflow.project.port.memory.*
import frflow.project.process.{Command, Output}
import frflow.project.program.{Analyse, Ports, Project, TestProgram}
import frflow.proof.layout.LeanWorkspace
import frflow.testing.Settings
import frflow.testing.report.Outcome
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** Rooms end to end (`sbt Lean/test`): its Lean written to a project on disk, with the developer's proof of
  * `grantWhenFree`'s step (`resources/rooms`), and checked by Lean's `lake`; its calendar's Scala tested with today's
  * settings (1,000 cases from seed 1), and the booking table kept in memory against the table's model (200 runs, an
  * outside system's); each node's standing compared with today's (`reference/rooms/standings.tsv`): what it stands
  * on (proven, tested, assumed), its check's status and its cases. Where they differ, the difference is listed below
  * with why; a second check then runs no Lean, every check current.
  */
class RoomsLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes

  /** A node as the standings compare it: kind; standing (assumed, tested where its tests checked it, else as its
    * check); its check's status; the cases its tests checked.
    */
  private def row(a: Analysis, id: NodeId): List[String] =
    val n = a.decided.theory.node(id).getOrElse(fail(id.value))
    val status = a.current(id).fold("")(_.status.toString.toLowerCase)
    val checked = a.tested(id).filter(r => r.outcome match
      case Outcome.NotChecked(_) => false
      case _                     => true)
    val standing =
      if n.statement.kind == NodeKind.Assumption then "assumed" else checked.fold(status)(_ => "tested")
    List(n.statement.kind.toString.toLowerCase, standing, status, checked.fold("")(_.cases.toString))

  private def reference: Map[String, List[String]] =
    val lines = Files.readAllLines(Path.of("reference/rooms/standings.tsv")).toArray.toList.map(_.toString)
    lines.drop(1).map(_.split("\t", -1).toList).map(cs => cs.head -> List(cs(1), cs(2), cs(3), cs(6))).toMap

  /** Where rooms now stands apart from today, each for a reason the design gives. */
  private val differences: Map[String, List[String]] = Map(
    // Today's proofs of the code's steps are authored (lean/Proofs); rooms' are ported with the Lean spike's in
    // step 11 (`book`'s impl for both roots, cover_book, made_inRoom): open until then, root_impl with them.
    "AnswerWhenFree" -> List("claim", "open", "open", ""),
    "BookWhenFree" -> List("claim", "open", "open", ""),
    "NeverOverlap" -> List("claim", "open", "open", ""),
    "RoomBookingsApart" -> List("claim", "open", "open", ""),
    // An assumption about the outside (a store behaving as its model) has no Lean check of its own; its 200 runs
    // against the model are as today's.
    "TableMatchesModel" -> List("assumption", "assumed", "", "200"))

  private def proof: String =
    scala.io.Source.fromResource("rooms/grantWhenFree.lean", getClass.getClassLoader)(using scala.io.Codec.UTF8)
      .mkString

  /** A directory for the project, deleted with everything in it once the test is done. */
  private val directory: Resource[IO, Path] = Resource.make(IO.blocking(Files.createTempDirectory("frflow-rooms")))(
    d => IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))))

  test("rooms checked by Lean and tested stands as today, but where the design says it differs".tag(Live)) {
    assert(LeanWorkspace.libraryBuilt._1, LeanWorkspace.libraryBuilt._2)
    val (e, examples) = (Projects.rooms, Projects.roomsExamples)
    val models = Tables.outside(e).toList
    assertEquals(models.map(_.node), List(NodeId("tableMatchesModel")))
    (for
      dir  <- directory
      lake <- Lake.make[IO](dir.resolve("lean"), Command("lake", 30.minutes, Output.Merged))
    yield (dir, lake)).use { (dir, lake) =>
      val files = ProjectFiles.make[IO](dir)
      val run = RunCode.make[IO]
      for
        library <- LeanLibrary.read[IO](LeanWorkspace.library, LeanWorkspace.library.toString)
        project  = Project(Nil, Settings.default, library)
        ledger  <- MemoryLedger[IO](Ledger.empty)
        git     <- MemoryGit[IO]
        keys    <- MemoryKeys[IO]
        ports    = Ports(files, ledger, git, keys)
        _       <- files.writeIfChanged(RelPath.fromIdentifiers("lean", "Proofs/Rooms/grantWhenFree.lean"), proof)
        a       <- Analyse(ports, run, project)(e, examples)
        (_, c)  <- CheckProgram(files, lake, library.path, run)(a, None)
        (_, t)  <- TestProgram[IO](files, run, models)(c, None)
        again   <- Analyse(ports, run, project)(e, examples)
        (r, _)  <- CheckProgram(files, lake, library.path, run)(again, None)
      yield
        val now = t.decided.theory.nodes.map(_.node.id).map(id => id.value.capitalize -> row(t, id)).toMap
        val compared = reference.keys.toList.sorted.filter(k => now.get(k) != reference.get(k))
          .map(k => k -> now.getOrElse(k, Nil))
        val table = now.toList.sortBy(_._1).map((k, v) => (k :: v).mkString("\t")).mkString("\n")
        assertEquals(compared.toMap, differences, s"rooms now:\n$table")
        assert(t.wholeCheck.isDefined, "the theory's own check is recorded")
        assertEquals(r, Nil)
    }
  }
