package rooms

import cats.effect.{IO, Ref, Resource}
import cats.syntax.all.*
import frflow.api.{Adapter, FrFlowApi, OnDisk, Opened, Project}
import frflow.cli.{Cli, Scripted}
import frflow.cli.command.Command
import frflow.core.example.Example
import frflow.cli.text.Depth
import frflow.core.name.{NodeId, RelPath}
import frflow.dsl.kb.FrModel
import frflow.project.{Live, Projects, Tables}
import frflow.project.port.{Lake, LeanLibrary}
import frflow.project.process.{Command as Process, Output}
import frflow.proof.layout.LeanWorkspace
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*
import scala.util.chaining.*

/** The README's walk-through of rooms replayed on the port (ARCHITECTURE section 9, `WalkthroughSuite`): rooms
  * checked and accepted, then each change on its own, `check`, `status` and `review` (skipping) after each, compared
  * line by line with `reference/rooms/walkthrough` where the design keeps today's text (`Walkthrough`).
  */
class WalkthroughSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val directory: Resource[IO, Path] = Resource.make(IO.blocking(Files.createTempDirectory("frflow-walk")))(
    d => IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))))

  private val adapter: Adapter[IO] = Adapter(storedBookings.checkedAgainst(
    start = (bs: List[Booking]) => Ref[IO].of(bs).map(Tables(_)), observe = (t: Tables) => t.bookings))

  private def project(kb: FrModel, examples: List[Example]): Project[IO] =
    Project(Projects.elaborated(kb), examples, List(adapter), List(Projects.sources), LeanWorkspace.library)

  private def examples(e: frflow.dsl.example.FrFlowExamples): List[Example] =
    e.elaborated.fold(es => throw AssertionError(es.toString), identity)

  /** What `check`, `status` and `review` (skipping each node) print, and their exit codes; what moved under a root
    * (`diff`), and how the calendar's claim is shown, with the rules it uses (`show`).
    */
  private def said(api: FrFlowApi[IO]): IO[Map[String, String]] =
    for
      (cs, check)  <- Cli.all(api, Command.Check(None, json = false))
      (ss, status) <- Cli.all(api, Command.Status(json = false))
      term         <- Scripted(List.fill(40)("s"))
      code         <- Cli.run(api, term, Command.Review(Some("ann")))
      review       <- term.text
      (_, diff)    <- Cli.all(api, Command.Diff(NodeId("bookWhenFree")))
      (_, show)    <- Cli.all(api, Command.Show(NodeId("grantWhenFree"), Depth.Normal))
    yield Map("check" -> s"$check\n--- exit ${cs.head.code}", "status" -> s"$status\n--- exit ${ss.head.code}",
      "review" -> s"$review\n--- exit ${code.code}", "diff" -> diff, "show" -> show)

  test("the walk-through's three changes fail as today's, on the port".tag(Live)) {
    assert(LeanWorkspace.libraryBuilt._1, LeanWorkspace.libraryBuilt._2)
    directory.flatMap(d => Lake.make[IO](d.resolve("lean"), Process("lake", 30.minutes, Output.Merged))
      .map(d -> _)).use { (dir, lake) =>
      for
        library <- LeanLibrary.read[IO](LeanWorkspace.library, LeanWorkspace.library.toString)
        ports   <- OnDisk.ports(dir)
        _       <- Walkthrough.proofs.traverse_((n, text) =>
                     ports.files.writeIfChanged(RelPath.fromIdentifiers("lean", s"Proofs/Rooms/$n.lean"), text))
        steps    = Walkthrough.steps(project, examples)
        base    <- OnDisk.api(steps.head._2, ports, lake, library.version)
        _       <- Opened.acceptAll(base)
        texts   <- steps.traverse((name, p) => OnDisk.api(p, ports, lake, library.version).flatMap(said)
                     .map(name -> _))
      yield texts.foreach(judge)
    }
  }

  /** The step's text against its golden, and today's against the port's, every difference judged; with
    * `FRFLOW_WALK` set, the texts are written there instead (to make the goldens).
    */
  private def judge(step: String, said: Map[String, String]): Unit =
    sys.env.get("FRFLOW_WALK") match
      case Some(out) =>
        said.foreach((what, text) => Files.createDirectories(Path.of(out, step))
          .pipe(_ => Files.writeString(Path.of(out, step, s"$what.txt"), Walkthrough.normal(text))))
      case None =>
        said.foreach((what, text) =>
          assertNoDiff(Walkthrough.normal(text), Walkthrough.golden(step, what), s"$step $what"))
        val found = Walkthrough.differences(step, said("check"), said("status"))
        assertEquals(found, WalkthroughDifferences.judged(step).map(_._1), s"$step: the differences from today's")
