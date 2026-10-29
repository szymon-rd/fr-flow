package rooms

import cats.data.NonEmptyList
import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.NodeKind
import frflow.decision.ledger.Ledger
import frflow.project.{Live, Projects, Tables}
import frflow.project.check.CheckProgram
import frflow.project.pipeline.Analysis
import frflow.project.port.*
import frflow.project.port.memory.*
import frflow.project.process.{Command, Output}
import frflow.project.program.{Analyse, Ports, Project, TestProgram}
import frflow.proof.lean.ast.{ModuleName, Names}
import frflow.proof.layout.LeanWorkspace
import frflow.proof.audit.Completeness
import frflow.proof.verdict.ProverRun
import frflow.testing.Settings
import frflow.testing.report.Outcome
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** Rooms ported as section 3 writes it, against today's (`reference/rooms`, ARCHITECTURE section 9, equivalence):
  * every difference in where a node sits and what it assumes is listed and judged; checked by Lean and tested (1,000
  * cases of the calendar and 200 runs of the table, from seed 1, as today), each node stands as today's but where
  * judged; and no statement is weakened: each claim as today stated it is proven equivalent to the port's
  * (`resources/rooms/port/Port.lean`). The seeded bugs are the README's changes (`WalkthroughSuite`).
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes
  private val t = Projects.rooms.theory

  /** Each difference from today's rooms, with why the design makes it. */
  private val judged: Map[String, (String, String)] = Map(
    "onlyBookingWrites" -> ("gone" ->
      "the programs changing a store are derived from the code, so no assumption lists them (owner §31)"),
    "bookWhenFree" -> ("neverOverlap is a rule below it, not a part" ->
      "a rule is no part of a step: Lean has it of every world already (2.4, owner §27)"),
    "acceptWhenFree" -> ("neverOverlap is a rule below it, not a part" ->
      "a rule is no part of a step: Lean has it of every world already (2.4, owner §27)"),
    "grantWhenFree" -> ("bookingsOfTheRoom, roomBookingsApart are rules below it, not parts" ->
      "a rule is no part of a step: Lean has it of every room's bookings already (2.4, owner §27)"),
    "tableMatchesModel" -> ("gone" ->
      ("no store behaves as a model: an operation's meaning is its model's, by op.means (owner §36); what it said of " +
        "the world outside, that nothing else writes the table, is nothingElseWrites")),
    "nothingElseWrites" -> ("new" ->
      ("said of storedBookings (owner §36): nothing outside the code writes its state; the table's Scala is tested " +
        "against the model under it, as today's 200 runs")),
    "storeWhenFree" -> ("assumes -tableMatchesModel" ->
      ("a run rests on its model being atomic alone; the table's Scala tested against the model is said of it " +
        "(owner §36)")),
    "answerWhenFree" -> ("assumes -tableMatchesModel" ->
      ("a run rests on its model being atomic alone; the table's Scala tested against the model is said of it " +
        "(owner §36)")),
    "neverOverlap" -> ("assumes +nothingElseWrites -onlyBookingWrites" ->
      ("its cover_book runs on the table's model, nothing else writing it; who changes the table is derived " +
        "(owner §27, §31)")),
    "bookingsOfTheRoom" -> ("assumes +bookingsEndAfterStart" ->
      ("proven by made_inRoom on a world of stored bookings, not inside storeWhenFree's step (2.6); a model's own " +
        "operation gives no premise (owner §36)")),
    "roomBookingsApart" -> ("assumes +bookingsEndAfterStart" ->
      ("proven by made_inRoom on a world of stored bookings, not inside storeWhenFree's step (2.6); a model's own " +
        "operation gives no premise (owner §36)")))

  /** Where each node differs from today's: gone, rules no longer parts, premises added or dropped. */
  private def differences: Map[String, String] =
    val now = t.nodes.map(_.node.id.value)
    val gone = Reference.nodes.filterNot(now.contains).map(_ -> "gone")
    val added = now.filterNot(Reference.nodes.contains).map(_ -> "new")
    val moved = now.filter(Reference.nodes.contains).flatMap { n =>
      val id = NodeId(n)
      val (parts, rules) = (t.refinement.parts(id).map(_.value), t.refinement.rules(id).map(_.value))
      val wasParts = Reference.parts(n)
      val assumes = t.refinement.assumed(id).map(_.value)
      val (added, dropped) = (assumes.filterNot(Reference.assumes(n).contains),
        Reference.assumes(n).filterNot(assumes.contains))
      List(
        Option.when(rules.nonEmpty && rules.forall(wasParts.contains) && parts == wasParts.filterNot(rules.contains))(
          s"${rules.mkString(", ")} ${if rules.size == 1 then "is a rule" else "are rules"} below it, not " +
            (if rules.size == 1 then "a part" else "parts")),
        Option.when(added.nonEmpty || dropped.nonEmpty)("assumes " + (added.map("+" + _) ++
          dropped.map("-" + _)).mkString(" "))).flatten.map(n -> _)
    }
    (gone ++ added ++ moved).toMap

  test("every difference from today's rooms in where a node sits and what it assumes is listed and judged") {
    assertEquals(Reference.nodes.size - t.nodes.size, 1)
    assertEquals(differences, judged.view.mapValues(_._1).toMap)
  }

  private def row(a: Analysis, id: NodeId): List[String] =
    val n = a.decided.theory.node(id).getOrElse(fail(id.value))
    val status = a.current(id).fold("")(_.status.toString.toLowerCase)
    // A model's runs are read by the model: shown, as today's, beside the assumption about the outside.
    val model = Option.when(n.statement.kind == NodeKind.Assumption)(a.models(id)).toList.flatten
    val checked = a.tested(id).orElse(model.headOption.flatMap(a.testedModel)).filter(r => r.outcome match
      case Outcome.NotChecked(_) => false
      case _                     => true)
    val standing =
      if n.statement.kind == NodeKind.Assumption then "assumed" else checked.fold(status)(_ => "tested")
    List(n.statement.kind.toString.toLowerCase, standing, status, checked.fold("")(_.cases.toString))

  /** Where each node stands apart from today, each for a reason the design gives. */
  private val standings: Map[String, List[String]] = Map(
    // Gone: the programs changing a store are derived (owner §31).
    "OnlyBookingWrites" -> Nil,
    // Gone: no store behaves as a model (owner §36); what it said of the outside is NothingElseWrites.
    "TableMatchesModel" -> Nil,
    // An assumption about the outside has no Lean check of its own; the table's Scala, tested against the model
    // under it, runs 200 times, as today's.
    "NothingElseWrites" -> List("assumption", "assumed", "", "200"))

  private def resource(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

  /** The developer's proofs (`resources/rooms/proofs`): the code's steps, the calendar's, what the table keeps. */
  private val proofs: List[String] =
    List("Lemmas", "storeWhenFree", "answerWhenFree", "grantWhenFree", "neverOverlap", "roomBookingsApart")

  private val directory: Resource[IO, Path] = Resource.make(IO.blocking(Files.createTempDirectory("frflow-rooms")))(
    d => IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))))

  private def lean(name: String): ModuleName = ModuleName(Names.path(name.split('.').toList*))

  test("checked by Lean and tested, each node stands as today's but where judged; no statement is weakened".tag(Live)) {
    assert(LeanWorkspace.libraryBuilt._1, LeanWorkspace.libraryBuilt._2)
    val models = Tables.sqlite(Projects.rooms)
    (for
      dir  <- directory
      lake <- Lake.make[IO](dir.resolve("lean"), Command("lake", 30.minutes, Output.Merged))
    yield (dir, lake)).use { (dir, lake) =>
      val files = ProjectFiles.make[IO](dir)
      val run = RunCode.make[IO]
      def write(path: String, text: String) = files.writeIfChanged(RelPath.fromIdentifiers("lean", path), text)
      for
        library <- LeanLibrary.read[IO](LeanWorkspace.library, LeanWorkspace.library.toString)
        project  = Project(Nil, Settings.default, library)
        ledger  <- MemoryLedger[IO](Ledger.empty)
        git     <- MemoryGit[IO]
        keys    <- MemoryKeys[IO]
        ports    = Ports(files, ledger, git, keys)
        _       <- proofs.traverse_(n => write(s"Proofs/Rooms/$n.lean", resource(s"rooms/proofs/$n.lean")))
        a       <- Analyse(ports, run, project)(Projects.rooms, Projects.roomsExamples)
        (_, c)  <- CheckProgram(files, lake, library.path, run)(a, None)
        (_, t)  <- TestProgram[IO](files, run, models)(c, None)
        _       <- Reference.oldLean.traverse_((p, text) => write(s"FrFlowGen/Old/$p", text))
        _       <- write("FrFlowGen/Port.lean", resource("rooms/port/Port.lean"))
        port    <- lake.build(NonEmptyList.one(lean("FrFlowGen.Port")))
      yield
        val now = t.decided.theory.nodes.map(_.node.id).map(id => id.value.capitalize -> row(t, id)).toMap
        val reference = Reference.standings
        val compared = (reference.keys ++ now.keys).toList.distinct.sorted.filter(k => now.get(k) != reference.get(k))
          .map(k => k -> now.getOrElse(k, Nil))
        val table = now.toList.sortBy(_._1).map((k, v) => (k :: v).mkString("\t")).mkString("\n")
        assertEquals(compared.toMap, standings, s"rooms now:\n$table")
        assert(t.wholeCheck.isDefined, "the theory's own check is recorded")
        assertEquals(Completeness.of(t.decided, t.modules), Nil)
        val said = port match
          case ProverRun.Built(o) => o
          case other              => fail(s"the claims are not shown equivalent to today's: $other")
        assert(!said.contains("sorryAx") && said.contains("'Port.grantWhenNoOverlap' depends on axioms"), said)
    }
  }
