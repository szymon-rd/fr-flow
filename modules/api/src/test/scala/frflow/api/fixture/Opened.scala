package frflow.api.fixture

import cats.effect.IO
import frflow.api.*
import frflow.api.shell.{Memory, ScriptedRocq, Session}
import frflow.api.view.{CheckEvent, View}
import frflow.core.example.Example
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.rules.Command
import frflow.dsl.kb.FrModel
import frflow.project.pipeline.Analysis
import frflow.project.program.Ports
import frflow.project.Projects
import fs2.Stream
import java.nio.file.Path

/** Projects opened in memory for the API's suites: no Rocq, git or disk. A session is opened over ports a test holds
  * (so two versions of a model can share one ledger, or a test can read the files written).
  */
object Opened:
  val sources: RelPath = Projects.sources
  val rocq: Rocq = Rocq.Proving(Set.empty, Set.empty)

  def project(kb: FrModel, examples: List[Example] = Nil): Project =
    Project(Projects.elaborated(kb), examples, List(sources), Path.of("../../rocq"))

  lazy val rooms: Project =
    Project(Projects.rooms, Projects.roomsExamples, List(sources), Path.of("../../rocq"))

  lazy val before: Project = project(Shelf.Before.kb)
  lazy val after: Project = project(Shelf.After.kb)
  lazy val trusted: Project = project(Shelf.Trusted.kb)
  lazy val lone: Project = project(Shelf.Lone.kb)

  def api(p: Project, decider: Option[String] = Some("ann"), rocq: Rocq = rocq): IO[FrFlowApi[IO]] =
    FrFlowApi.inMemory[IO](p, Map.empty, decider, rocq)

  def ports(files: Map[RelPath, String] = Map.empty, decider: Option[String] = Some("ann")): IO[Ports[IO]] =
    Memory.ports[IO](files, decider)

  def session(p: Project, ports: Ports[IO], rocq: Rocq = rocq): Session[IO] =
    Session[IO](p, ports, ScriptedRocq[IO](rocq), Memory.run)

  def over(p: Project, ports: Ports[IO], rocq: Rocq = rocq): IO[FrFlowApi[IO]] = Memory.api(session(p, ports, rocq))

  def analysis(p: Project, ports: Ports[IO]): IO[Analysis] = session(p, ports).analysis

  /** Every node checked (its code tested: untested code is not accepted), then accepted at once, parents first. */
  def acceptAll(api: FrFlowApi[IO]): IO[Unit] = checked(api.proving.check(None)).flatMap(v =>
    api.deciding.decide(Command.Accept(v.nodes.map(_.id), "it says what the service must do", Nil, Map.empty), "ann")
      .flatMap(out => IO.raiseUnless(out.isRight)(AssertionError(out.toString))))

  /** A check run to its end: its events. */
  def events(s: Stream[IO, CheckEvent]): IO[List[CheckEvent]] = s.compile.toList

  /** The view a check ends with. */
  def checked(s: Stream[IO, CheckEvent]): IO[View] = events(s).flatMap(_.collectFirst {
    case CheckEvent.Done(_, v) => v
  }.fold(IO.raiseError(AssertionError("no Done")))(IO.pure))

  def id(s: String): NodeId = NodeId(s)
